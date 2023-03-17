#include <assert.h>
#include <dlfcn.h>
#include <malloc.h>
#include <mcheck.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/param.h>
#include <sys/shm.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/time.h>

#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <time.h>
#include <ucontext.h>
#include <unistd.h>
#include <float.h>
#include <stdio.h>
#include <math.h>
#define NOISY_BINARY_SEARCH_ENV_VAR "NOISY_BINARY_SEARCH"

typedef struct {
  double mean;
  double M2;
  uint64_t sat;
  uint64_t count;
  uint64_t time;
  uint8_t typ;
} BranchCmp;

enum Predicate {
  FCMP_FALSE =  0,  ///< 0 0 0 0    Always false (always folded)
  FCMP_OEQ   =  1,  ///< 0 0 0 1    True if ordered and equal
  FCMP_OGT   =  2,  ///< 0 0 1 0    True if ordered and greater than
  FCMP_OGE   =  3,  ///< 0 0 1 1    True if ordered and greater than or equal
  FCMP_OLT   =  4,  ///< 0 1 0 0    True if ordered and less than
  FCMP_OLE   =  5,  ///< 0 1 0 1    True if ordered and less than or equal
  FCMP_ONE   =  6,  ///< 0 1 1 0    True if ordered and operands are unequal
  FCMP_ORD   =  7,  ///< 0 1 1 1    True if ordered (no nans)
  FCMP_UNO   =  8,  ///< 1 0 0 0    True if unordered: isnan(X) | isnan(Y)
  FCMP_UEQ   =  9,  ///< 1 0 0 1    True if unordered or equal
  FCMP_UGT   = 10,  ///< 1 0 1 0    True if unordered or greater than
  FCMP_UGE   = 11,  ///< 1 0 1 1    True if unordered, greater than, or equal
  FCMP_ULT   = 12,  ///< 1 1 0 0    True if unordered or less than
  FCMP_ULE   = 13,  ///< 1 1 0 1    True if unordered, less than, or equal
  FCMP_UNE   = 14,  ///< 1 1 1 0    True if unordered or not equal
  FCMP_TRUE  = 15,  ///< 1 1 1 1    Always true (always folded)
  FIRST_FCMP_PREDICATE = FCMP_FALSE,
  LAST_FCMP_PREDICATE = FCMP_TRUE,
  BAD_FCMP_PREDICATE = FCMP_TRUE + 1,
  ICMP_EQ    = 32,  ///< equal
  ICMP_NE    = 33,  ///< not equal
  ICMP_UGT   = 34,  ///< unsigned greater than
  ICMP_UGE   = 35,  ///< unsigned greater or equal
  ICMP_ULT   = 36,  ///< unsigned less than
  ICMP_ULE   = 37,  ///< unsigned less or equal
  ICMP_SGT   = 38,  ///< signed greater than
  ICMP_SGE   = 39,  ///< signed greater or equal
  ICMP_SLT   = 40,  ///< signed less than
  ICMP_SLE   = 41,  ///< signed less or equal
  FIRST_ICMP_PREDICATE = ICMP_EQ,
  LAST_ICMP_PREDICATE = ICMP_SLE,
  BAD_ICMP_PREDICATE = ICMP_SLE + 1
};

double compute_prob(uint32_t br_id, BranchCmp* val) {
      if (val->sat > 0) {
          return (double) val->sat/ (double) val->count;
      }

      double m = (double) val->mean;
      double var = ((double) val->M2 / (double) val->count ); 
      if (val->count == 1) {
          var = 0.0;
      }
      double ratio = 0.0;
      double shift;
      if (true) { // integer only for now
          shift = 1.0;
      } else {
          shift = DBL_MIN;
      }
      double epsilon = 0.001; // 10^-3

      switch (val->typ) { 
        case FCMP_OEQ:
        case FCMP_UEQ:
        case ICMP_EQ: {  /* equal */
            double ratio1 = var / (var +m*m);
            double ratio2 = var / (var +m*m);
            ratio = ratio1;
            break;
        }
        case FCMP_ONE:
        case FCMP_UNE:
        case ICMP_NE: {  /* not equal */
            double ratio1 = var / (var +(m-shift)*(m-shift));
            double ratio2 = var / (var +(m+shift)*(m+shift));
            ratio = ratio1 + ratio2;
            break;
        }
        case FCMP_OGT:
        case FCMP_UGT:
        case ICMP_SGT:
        case ICMP_UGT: { /* unsigned greater than */
            ratio = var / (var +(m-shift)*(m-shift));
            break;
        }
        case FCMP_OGE:
        case FCMP_UGE:
        case ICMP_SGE:
        case ICMP_UGE: { /* unsigned greater or equal */
            ratio = var / (var +m*m);
            break;
        }
        case FCMP_OLT:
        case FCMP_ULT:
        case ICMP_SLT:
        case ICMP_ULT: { /* unsigned less than */
            ratio = var / (var +(m+shift)*(m+shift));
            break;
        }
        case FCMP_OLE:
        case FCMP_ULE:
        case ICMP_SLE:
        case ICMP_ULE: { /* unsigned less or equal */
            ratio = var / (var +(m+shift)*(m+shift));
            break;
        }
        default: {
            break;
        }   
     }
    assert(ratio >= 0.0);
    assert(ratio <= 1.0);
    return ratio;
}

typedef struct {
  uint8_t low;
  uint8_t high;
} Interval;

typedef struct {
  uint64_t size;
  Interval *interval;
} Hyperrectangle;

typedef struct {
  uint8_t direction;
} BranchSequence;

static BranchSequence *branch_policy;
static uint64_t branch_policy_branches_cnt = 0;
static uint64_t fx_count = 0;
static bool montecarlo_execing = 0;


static BranchCmp *branch_cmp;
static uint32_t *branch_cmp_seen;
static uint64_t g_time = 0;
static bool tracing = 0;

static const uint32_t maxpossibleBBs = 4000;
static const uint32_t maxseenBBs = 1000;
static void *mmap_start = (void *)0x200000;
static uint64_t executed_branches_cnt = 0;
static bool setup_initialized = 0;
static bool fork_servering = 0;
static int32_t child_pid = -1;
static const uint64_t branch_policy_size =
    ((maxpossibleBBs + 1) * sizeof(BranchSequence));
static const uint64_t branch_cmp_size =
    ((maxpossibleBBs + 1) * 2 * sizeof(BranchCmp));
static const uint64_t branch_cmp_seen_size =
    ((maxseenBBs + 1) * sizeof(uint32_t));

void reset_per_execution_metadata(void) {
  g_time = 0;
  executed_branches_cnt = 0;
  branch_policy_branches_cnt = 0;
  fx_count = 0;
}

void __attribute__((destructor)) teardown(void) {
  if (tracing && fork_servering == 0) {
    assert(fork_servering == 0);

    double min_ratio = 10;
    uint32_t i = 0;
    while (1) {
      uint32_t key = branch_cmp_seen[i];
      if (key == 0xffffffff) {
        break;
      }
      BranchCmp *val = &branch_cmp[key];
      double new_ratio = compute_prob(key, val);
      if (new_ratio <= min_ratio) {
          min_ratio = new_ratio;
      }
      i++;
    }
    printf("%f ratio \n", min_ratio);
  }
}

void update_branch(uint32_t br_id, bool ret_cond, bool is_sat , void *args0, void *args1,
                   uint8_t bitsize, uint8_t is_signed, uint8_t cond_type) {
  BranchCmp *bcmp = &branch_cmp[2 * br_id + ret_cond];

  if (bcmp->count == 0) {
    assert(g_time < maxseenBBs);
    branch_cmp_seen[g_time] = 2 * br_id + ret_cond;
    switch (bitsize) {
    case 8:
      if (is_signed) {
        bcmp->mean = (double)(*(int8_t *)args0) - (*(int8_t *)args1);
      } else {
        bcmp->mean = (double)(*(uint8_t *)args0) - (*(uint8_t *)args1);
      }
      break;
    case 16:
      if (is_signed) {
        bcmp->mean = (double)(*(int16_t *)args0) - (*(int16_t *)args1);
      } else {
        bcmp->mean = (double)(*(uint16_t *)args0) - (*(uint16_t *)args1);
      }
      break;
    case 32:
      if (is_signed) {
        bcmp->mean = (double)(*(int32_t *)args0) - (*(int32_t *)args1);
      } else {
        bcmp->mean = (double)(*(uint32_t *)args0) - (*(uint32_t *)args1);
      }
      break;
    case 64:
      if (is_signed) {
        bcmp->mean = (double)(*(int64_t *)args0) - (*(int64_t *)args1);
      } else {
        bcmp->mean = (double)(*(uint64_t *)args0) - (*(uint64_t *)args1);
      }
      break;
    }
    bcmp->count = 1;
    bcmp->sat = is_sat;
    assert(cond_type > 0);
    bcmp->typ = cond_type;
    bcmp->M2 = 0.0;
    bcmp->time = g_time;
    g_time++;
  } else {
    bcmp->count++;
    bcmp->sat += is_sat;
    double delta;
    switch (bitsize) {
    case 8:
      if (is_signed) {
        delta = ((double)(*(int8_t *)args0) - (*(int8_t *)args1)) - bcmp->mean;
      } else {
        delta =
            ((double)(*(uint8_t *)args0) - (*(uint8_t *)args1)) - bcmp->mean;
      }
      break;
    case 16:
      if (is_signed) {
        delta =
            ((double)(*(int16_t *)args0) - (*(int16_t *)args1)) - bcmp->mean;
      } else {
        delta =
            ((double)(*(uint16_t *)args0) - (*(uint16_t *)args1)) - bcmp->mean;
      }
      break;
    case 32:
      if (is_signed) {
        delta =
            ((double)(*(int32_t *)args0) - (*(int32_t *)args1)) - bcmp->mean;
      } else {
        delta =
            ((double)(*(uint32_t *)args0) - (*(uint32_t *)args1)) - bcmp->mean;
      }
      break;
    case 64:
      if (is_signed) {
        delta =
            ((double)(*(int64_t *)args0) - (*(int64_t *)args1)) - bcmp->mean;
      } else {
        delta =
            ((double)(*(uint64_t *)args0) - (*(uint64_t *)args1)) - bcmp->mean;
      }
      break;
    }
    bcmp->mean += delta / (bcmp->count);
    double delta2;
    switch (bitsize) {
    case 8:
      if (is_signed) {
        delta2 = ((double)(*(int8_t *)args0) - (*(int8_t *)args1)) - bcmp->mean;
      } else {
        delta2 =
            ((double)(*(uint8_t *)args0) - (*(uint8_t *)args1)) - bcmp->mean;
      }
      break;
    case 16:
      if (is_signed) {
        delta2 =
            ((double)(*(int16_t *)args0) - (*(int16_t *)args1)) - bcmp->mean;
      } else {
        delta2 =
            ((double)(*(uint16_t *)args0) - (*(uint16_t *)args1)) - bcmp->mean;
      }
      break;
    case 32:
      if (is_signed) {
        delta2 =
            ((double)(*(int32_t *)args0) - (*(int32_t *)args1)) - bcmp->mean;
      } else {
        delta2 =
            ((double)(*(uint32_t *)args0) - (*(uint32_t *)args1)) - bcmp->mean;
      }
      break;
    case 64:
      if (is_signed) {
        delta2 =
            ((double)(*(int64_t *)args0) - (*(int64_t *)args1)) - bcmp->mean;
      } else {
        delta2 =
            ((double)(*(uint64_t *)args0) - (*(uint64_t *)args1)) - bcmp->mean;
      }
      break;
    }
    bcmp->M2 += delta * delta2;
  }
}

bool log_funchelper(uint32_t br_id, bool old_cond, void *args0, void *args1,
                    uint8_t bitsize, uint8_t is_signed, uint8_t cond_type) {
  assert(br_id < maxpossibleBBs);
  bool ret_cond;
  if (!setup_initialized) {
    return old_cond;
  }

  if (montecarlo_execing) {
    BranchSequence *const bseq = &branch_policy[br_id];
    ret_cond = bseq->direction;
    if (ret_cond != old_cond) {
      fx_count++;
    }

  } else {
    ret_cond = old_cond;
  }

  if (tracing) {
    update_branch(br_id, ret_cond, ret_cond == old_cond, args0, args1, bitsize, is_signed, cond_type);
  }
  executed_branches_cnt++;
  return ret_cond;
}

bool log_func8(uint32_t br_id, bool old_cond, uint8_t arg1, uint8_t arg2,
               uint8_t is_signed, uint8_t cond_type) {
  uint8_t args[2];
  args[0] = arg1;
  args[1] = arg2;
  return log_funchelper(br_id, old_cond, (void *)&args[0], (void *)&args[1], 8,
                        is_signed, cond_type);
}

bool log_func16(uint32_t br_id, bool old_cond, uint16_t arg1, uint16_t arg2,
                uint8_t is_signed, uint8_t cond_type) {
  uint16_t args[2];
  args[0] = arg1;
  args[1] = arg2;
  return log_funchelper(br_id, old_cond, (void *)&args[0], (void *)&args[1], 16,
                        is_signed, cond_type);
}

bool log_func64(uint32_t br_id, bool old_cond, uint64_t arg1, uint64_t arg2,
                uint8_t is_signed, uint8_t cond_type) {
  uint64_t args[2];
  args[0] = arg1;
  args[1] = arg2;
  return log_funchelper(br_id, old_cond, (void *)&args[0], (void *)&args[1], 64,
                        is_signed, cond_type);
}

bool log_func32(uint32_t br_id, bool old_cond, uint32_t arg1, uint32_t arg2,
                uint8_t is_signed, uint8_t cond_type) {
  uint32_t args[2];
  args[0] = arg1;
  args[1] = arg2;
  return log_funchelper(br_id, old_cond, (void *)&args[0], (void *)&args[1], 32,
                        is_signed, cond_type);
}

void reset_shm_branch_cmp() { memset(branch_cmp, 0, branch_cmp_size); }
void setup_shm_branch_cmp() {
  int32_t shm_id_data =
      shmget(IPC_PRIVATE, branch_cmp_size, IPC_CREAT | IPC_EXCL | 0600);

  if (shm_id_data < 0) {
    printf("shmget() in setup_shm_branch_cmp() failed\n");
    exit(EXIT_FAILURE);
  }

  branch_cmp = shmat(shm_id_data, NULL, 0);

  if (!branch_cmp) {
    printf("shmat() in setup_shm_branch_cmp() failed\n");
    exit(EXIT_FAILURE);
  }
}

void reset_shm_branch_cmp_seen() {
  memset(branch_cmp_seen, 0xff, branch_cmp_seen_size);
}
void setup_shm_branch_cmp_seen() {
  int32_t shm_id_seen =
      shmget(IPC_PRIVATE, branch_cmp_seen_size, IPC_CREAT | IPC_EXCL | 0600);

  if (shm_id_seen < 0) {
    printf("shmget() in setup_shm_branch_cmp_seen() failed\n");
    exit(EXIT_FAILURE);
  }

  branch_cmp_seen = shmat(shm_id_seen, NULL, 0);

  if (!branch_cmp_seen) {
    printf("shmat() in setup_shm_branch_cmp_seen() failed\n");
    exit(EXIT_FAILURE);
  }
}
int counting_helper(Hyperrectangle *h, uint8_t *input, int fd) {
  uint8_t child_stopped = 0;
  int status;

  setup_shm_branch_cmp();
  setup_shm_branch_cmp_seen();
  reset_shm_branch_cmp();
  reset_shm_branch_cmp_seen();

  for (int i = 0; i < 5; i++) {
    for (uint64_t i = 0; i < h->size; i++) {
      input[i] = rand() % (h->interval[i].high - h->interval[i].low + 1) +
                h->interval[i].low;
    }
    lseek(fd, 0, SEEK_SET);
    if (write(fd, input, h->size) <= 0) {
      printf("ERROR; write failed \n");
      exit(EXIT_FAILURE);
    }

  child_pid = fork();
  if (child_pid < 0) {
    printf("failure to fork process \n");
    exit(EXIT_FAILURE);
  }
  if (!child_pid) {
    assert(fork_servering == 1);
    tracing = 1;
    return 1;
  }

    if (waitpid(child_pid, &status, 0) < 0) {
      printf("failure to wait for child \n");
      exit(EXIT_FAILURE);
    }

    if (WIFSTOPPED(status))
      child_stopped = 1;
  }
  return 0;
}

typedef struct {
  Hyperrectangle* h;
  double weight;
} weight_group;

static bool is_left;
static Hyperrectangle* promising_hyperrectangle;

void print_hyperrectangle(Hyperrectangle *h) {
    bool printed = false;
      for (uint64_t i = 0; i < h->size; i++) {
          if (h->interval[i].low == 0 && h->interval[i].high == 255) {
          } else {
              fprintf(stderr,"%lu: [%d, %d] ", i, h->interval[i].low, h->interval[i].high); 
              printed = true;
          }
      }
      if (printed) {
      } else {
          fprintf(stderr,"[0, 255]^%lu", h->size);
      }
      fprintf(stderr,"\n");
}

int noisy_counting_oracle(Hyperrectangle *iL, Hyperrectangle *iR, uint8_t *input, int fd) {
  
  int is_child = counting_helper(iL, input, fd);
  double iL_count = 1;
  if (is_child == 0) {
    uint32_t j = 0;
    while (1) {
      uint32_t key = branch_cmp_seen[j];
      if (key == 0xffffffff) {
        break;
      }
      BranchCmp *val = &branch_cmp[key];
      double tmp_count = compute_prob(key, val);
      if (iL_count > tmp_count) {
        iL_count = tmp_count;
      }
      j++;
    }
  } else {
    return is_child;
  }

  is_child = counting_helper(iR, input, fd);
  double iR_count = 1;
  if (is_child == 0) {
    uint32_t j = 0;
    while (1) {
      uint32_t key = branch_cmp_seen[j];
      if (key == 0xffffffff) {
        break;
      }
      BranchCmp *val = &branch_cmp[key];
      double tmp_count = compute_prob(key, val);
      if (iR_count > tmp_count) {
        iR_count = tmp_count;
      }
      j++;
    }
  } else {
    return is_child;
  }

  is_left = (iL_count >= iR_count);

  return 0;
}

int find_group(weight_group* groups, int number_of_weight_groups, double* wL) {
  double cumulative_weight = 0;
  int group_index;
  for (int i = 0; i < number_of_weight_groups; i++) {
    cumulative_weight += groups[i].weight;
    if (cumulative_weight > 0.5) {
      group_index = i;
      break;
    }
  }
  *wL = cumulative_weight - groups[group_index].weight;
  return group_index;
}

void create_new_weight_groups(weight_group* groups, int number_of_weight_groups, int group_index) {

  for (int i = number_of_weight_groups; i > group_index; i--) {
    groups[i] = groups[i - 1];
  }
  
  groups[group_index + 1].h = malloc(sizeof(Hyperrectangle));
  groups[group_index + 1].h->size = groups[group_index].h->size;
  groups[group_index + 1].h->interval = malloc(sizeof(Interval) * (groups[group_index + 1].h->size + 1));
  memcpy(groups[group_index + 1].h->interval, groups[group_index].h->interval, sizeof(Interval) * (groups[group_index + 1].h->size + 1));

  int dim = 0;
  while (dim < groups[group_index].h->size && groups[group_index].h->interval[dim].high == groups[group_index].h->interval[dim].low) {
    dim++;
  }

  int m = (groups[group_index].h->interval[dim].high + groups[group_index].h->interval[dim].low) / 2;
  groups[group_index].h->interval[dim].high = m;
  groups[group_index + 1].h->interval[dim].low = m + 1;
}

void update_weight_groups(weight_group* groups, 
                          int number_of_weight_groups, 
                          int group_index,
                          double p,
                          double Z, 
                          bool is_left) {
  
  for (int i = 0; i <= group_index; i++) {
    if (is_left) {
      groups[i].weight *= ((1 - p)/Z);
    } else {
      groups[i].weight *= (p/Z);
    }
  }
  for (int i = group_index + 1; i < number_of_weight_groups; i++) {
    if (is_left) {
      groups[i].weight *= (p/Z);
    } else {
      groups[i].weight *= ((1 - p)/Z);
    }
  }
}

bool terminate_search(weight_group* groups, int number_of_weight_groups) {
  double threshold = 1 / sqrt(groups[0].h->size * 8);
  for (int i = 0; i < number_of_weight_groups; i++) {
    uint64_t cardinality = 1;
    for (int j = 0; j < groups[i].h->size; j++) {
      cardinality *= (groups[i].h->interval[j].high - groups[i].h->interval[j].low + 1);
    }
    if (threshold < (groups[i].weight / cardinality)) {
      promising_hyperrectangle = groups[i].h;
      return true;
    }
  }
  return false;
}

void noisy_binary_search_(double p) {
  char *filename = getenv("INPUT_FILE");
  assert(filename);
  int fd = open(filename, O_RDWR);
  if (fd <= 0) {
    exit(EXIT_FAILURE);
  }
  struct stat st;
  if (fstat(fd, &st)) {
    exit(EXIT_FAILURE);
  }

  uint8_t *input = malloc(sizeof(uint8_t) * (st.st_size + 1));

  weight_group groups[1000];
  
  groups[0].h = malloc(sizeof(Hyperrectangle));
  groups[0].h->size = st.st_size;
  groups[0].h->interval = malloc(sizeof(Interval) * (groups[0].h->size + 1));
  for (int i = 0; i < groups[0].h->size; i++) {
    groups[0].h->interval[i].low = 0;
    groups[0].h->interval[i].high = 255;
  }
  groups[0].weight = 1;
  int number_of_weight_groups = 1;

  while (!terminate_search(groups, number_of_weight_groups)) {

    double wL = 0;
    int group_index = find_group(groups, number_of_weight_groups, &wL);

    create_new_weight_groups(groups, number_of_weight_groups, group_index);
    number_of_weight_groups++;

    int is_child = noisy_counting_oracle(groups[group_index].h, groups[group_index + 1].h, input, fd);
    if (is_child) {
      return;
    }

    double Z = (is_left)? ((wL + groups[group_index].weight) * (1 - p) + (1 - wL) * p) : ((wL + groups[group_index].weight) * p + (1 - wL) * (1 - p));
    
    update_weight_groups(groups, number_of_weight_groups, group_index, p, Z, is_left);
  }
  printf("--- Most Promising Input Region ----\n");
  print_hyperrectangle(promising_hyperrectangle);
  for (int i = 0; i < number_of_weight_groups; i++) {
    free(groups[i].h->interval);
    free(groups[i].h);
  }
  exit(0);
}

void __attribute__((constructor(0))) setup(void) {

  srand(17);

  if (getenv("MONTECARLO_EXE")) {
    branch_policy = (BranchSequence *)mmap(mmap_start, branch_policy_size,
                                           PROT_READ | PROT_WRITE,
                                           MAP_PRIVATE | MAP_ANON, -1, 0);
    if ((uint64_t)branch_policy == 0xffffffffffffffff) {
      printf("ERROR; could not allocate %lu bytes\n", branch_policy_size);
      exit(EXIT_FAILURE);
    }
    mmap_start += branch_policy_size;
    montecarlo_execing = 1;
    FILE *fp;
    char *line = NULL;
    size_t len = 0;
    ssize_t read;

    char *filename = getenv("MONTECARLO_EXE");
    fp = fopen(filename, "r");
    if (fp == NULL) {
      printf("ERROR; policy file not found %s\n", filename);
      exit(EXIT_FAILURE);
    }
    while ((read = getline(&line, &len, fp)) != -1) {
      char *tok = strtok(line, " ");
      uint32_t bbid = strtoul(tok, NULL, 10);

      BranchSequence *bseq = &branch_policy[bbid];
      tok = strtok(NULL, " ");
      bseq->direction = (unsigned char) strtoull(tok, NULL, 10);
      branch_policy_branches_cnt += 1;
    }
    fclose(fp);
    if (line)
      free(line);
  }
  if (getenv(NOISY_BINARY_SEARCH_ENV_VAR)) {
    fork_servering = 1;
  }
  if (getenv("COLLECT_COUNT")) {
    tracing = 1;
    branch_cmp =
        (BranchCmp *)mmap(mmap_start, branch_cmp_size, PROT_READ | PROT_WRITE,
                          MAP_PRIVATE | MAP_ANON, -1, 0);
    if ((uint64_t)branch_cmp == 0xffffffffffffffff) {
      printf("ERROR; could not allocate %lu bytes\n", branch_cmp_size);
      exit(EXIT_FAILURE);
    }
    mmap_start += branch_cmp_size;
    reset_shm_branch_cmp();

    branch_cmp_seen = (uint32_t *)mmap(mmap_start, branch_cmp_seen_size,
                                       PROT_READ | PROT_WRITE,
                                       MAP_PRIVATE | MAP_ANON, -1, 0);
    if ((uint64_t)branch_cmp_seen == 0xffffffffffffffff) {
      printf("ERROR; could not allocate %lu bytes\n", branch_cmp_seen_size);
      exit(EXIT_FAILURE);
    }
    mmap_start += branch_cmp_seen_size;
    reset_shm_branch_cmp_seen();
  }
  setup_initialized = true;
  if (getenv(NOISY_BINARY_SEARCH_ENV_VAR)) {
    noisy_binary_search_(0.01);
  }
}
