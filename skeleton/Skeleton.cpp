#include "llvm/Analysis/CFGPrinter.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Utils.h"
#include <iostream>
#include <set>

using namespace llvm;

namespace {
struct SkeletonPass : public ModulePass {
  static char ID;
  SkeletonPass() : ModulePass(ID) {}

  virtual void getAnalysisUsage(AnalysisUsage &AU) const override;
  virtual bool runOnModule(Module &F) override;
};
} // namespace
void SkeletonPass::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
}

bool SkeletonPass::runOnModule(Module &M) {
  LLVMContext &C = M.getContext();
  const DataLayout *DL = &M.getDataLayout();

  IntegerType *Int64Ty = IntegerType::getInt64Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);
  IntegerType *Int16Ty = IntegerType::getInt16Ty(C);
  IntegerType *Int8Ty = IntegerType::getInt8Ty(C);
  IntegerType *Int1Ty = IntegerType::getInt1Ty(C);

  FunctionCallee LogFunc[4];
  LogFunc[0] = M.getOrInsertFunction("log_func8", Int1Ty, Int32Ty, Int1Ty,
                                     Int8Ty, Int8Ty, Int8Ty, Int8Ty);
  LogFunc[1] = M.getOrInsertFunction("log_func16", Int1Ty, Int32Ty, Int1Ty,
                                     Int16Ty, Int16Ty, Int8Ty, Int8Ty);
  LogFunc[2] = M.getOrInsertFunction("log_func32", Int1Ty, Int32Ty, Int1Ty,
                                     Int32Ty, Int32Ty, Int8Ty, Int8Ty);
  LogFunc[3] = M.getOrInsertFunction("log_func64", Int1Ty, Int32Ty, Int1Ty,
                                     Int64Ty, Int64Ty, Int8Ty, Int8Ty);
  FunctionCallee FakeFunc = M.getOrInsertFunction("fake_func", Int1Ty, Int32Ty);
  FunctionCallee SwitchFunc =
      M.getOrInsertFunction("switch_func", Int64Ty, Int32Ty, Int64Ty);

  int br_cnt = 0;
  for (auto &F : M) {
    for (auto &BB : F) {
      Instruction *t_inst = BB.getTerminator();
      LLVMContext &C = t_inst->getContext();
      MDNode *N = MDNode::get(C, MDString::get(C, std::to_string(br_cnt)));

      std::string location = std::string("UNKNOWN");
      if (DILocation *Loc = t_inst->getDebugLoc().get()) {
        location = std::string(Loc->getFilename().data()) + std::string(":") +
                   std::to_string(Loc->getLine());
        MDNode *M = MDNode::get(C, MDString::get(C, location));
        t_inst->setMetadata("Loc", M);
      }
      t_inst->setMetadata("BB_ID", N);
      IRBuilder<> IRB(t_inst);
      IRB.CreateCall(FakeFunc, {ConstantInt::get(Int32Ty, br_cnt)});
      std::cout << "@@@ " << F.getName().str() << ", branch id: " << br_cnt
                << "| loc " << location << "\n";
      assert(br_cnt <
             2000000000);
      br_cnt += 1;
    }
  }
  int cur_br_id = 0;
  int br_id_1 = 0;
  int br_id_2 = 0;
  for (auto &F : M) {
    for (auto &BB : F) {

      for (auto &I : BB) {
        if (MDNode *N = BB.getTerminator()->getMetadata("BB_ID")) {
          cur_br_id =
              std::stoi(cast<MDString>(N->getOperand(0))->getString().str());
        } else {
          std::cout << "ERROR NO BRANCH ID!\n";
          assert(0);
        }
        if (BranchInst *br_inst = dyn_cast<BranchInst>(&I)) {
          IRBuilder<> IRB(br_inst);
          if (br_inst->isConditional()) {

            std::string true_cond;
            std::string false_cond;
            br_id_1 = std::stoi(cast<MDString>(br_inst->getSuccessor(0)
                                                   ->getTerminator()
                                                   ->getMetadata("BB_ID")
                                                   ->getOperand(0))
                                    ->getString()
                                    .str());
            br_id_2 = std::stoi(cast<MDString>(br_inst->getSuccessor(1)
                                                   ->getTerminator()
                                                   ->getMetadata("BB_ID")
                                                   ->getOperand(0))
                                    ->getString()
                                    .str());
            if (ICmpInst *cmp_inst =
                    dyn_cast<ICmpInst>(br_inst->getCondition())) {
              ICmpInst::Predicate pred = cmp_inst->getPredicate();
              int is_signed = -1;
	          assert(pred > 0);
	          assert(pred <= 255);
              uint8_t cond_type = pred;

              switch (pred) {
              case ICmpInst::ICMP_UGT:
                true_cond = "ICMP_UGT";
                false_cond = "ICMP_ULE";
                is_signed = 0;
                break;
              case ICmpInst::ICMP_SGT: // 001
                true_cond = "ICMP_SGT";
                false_cond = "ICMP_SLE";
                is_signed = 1;
                break;
              case ICmpInst::ICMP_EQ: // 010
                true_cond = "ICMP_EQ";
                false_cond = "ICMP_NE";
                is_signed = 0;
                break;
              case ICmpInst::ICMP_UGE: // 011
                true_cond = "ICMP_UGE";
                false_cond = "ICMP_ULT";
                is_signed = 0;
                break;
              case ICmpInst::ICMP_SGE: // 011
                true_cond = "ICMP_SGE";
                false_cond = "ICMP_SLT";
                is_signed = 1;
                break;
              case ICmpInst::ICMP_ULT: // 100
                true_cond = "ICMP_ULT";
                false_cond = "ICMP_UGE";
                is_signed = 0;
                break;
              case ICmpInst::ICMP_SLT: // 100
                true_cond = "ICMP_SLT";
                false_cond = "ICMP_SGE";
                is_signed = 1;
                break;
              case ICmpInst::ICMP_NE: // 101
                true_cond = "ICMP_NE";
                false_cond = "ICMP_EQ";
                is_signed = 0;
                break;
              case ICmpInst::ICMP_ULE: // 110
                true_cond = "ICMP_ULE";
                false_cond = "ICMP_UGT";
                is_signed = 0;
                break;
              case ICmpInst::ICMP_SLE: // 110
                true_cond = "ICMP_SLE";
                false_cond = "ICMP_SGT";
                is_signed = 1;
                break;
              default:
                true_cond = "NO_TYPE";
                false_cond = "NO_TYPE";
                std::cout << "ERROR NO ICMPTYPE!\n";
                assert(0);
                break;
              }
              std::cout << "@@@ edge id (" << cur_br_id << "," << br_id_1
                        << "), cond type " << true_cond << ", true\n";
              std::cout << "@@@ edge id (" << cur_br_id << "," << br_id_2
                        << "), cond type " << false_cond << ", false\n";
              Value *A0 = cmp_inst->getOperand(0);
              Value *A1 = cmp_inst->getOperand(1);
              if (!A0->getType()->isIntegerTy()) {
                if (A0->getType()->isPointerTy()) {
                  std::cout << cur_br_id << ", " << br_id_1 << ", " << br_id_2
                            << " pointer icmp: not an integer-valued icmp, but "
                               "still an icmp\n";
                  auto CallbackFunc = LogFunc[3];
                  auto Ty = Type::getIntNTy(C, 64);
                  assert(is_signed == 0);
                  Value *ret_val = IRB.CreateCall(
                      CallbackFunc,
                      {ConstantInt::get(Int32Ty, cur_br_id),
                       br_inst->getCondition(), A0, A1,
                       ConstantInt::get(
                           Int8Ty,
                           is_signed), ConstantInt::get(Int8Ty, cond_type)});
                  br_inst->setCondition(ret_val);
                } else {
                  std::string type_str;
                  llvm::raw_string_ostream rso(type_str);
                  A0->print(rso);
                  std::cout << rso.str() << " buggy instruction \n";
                  std::cout << "UNKNOWNERROR "
                            << " not an integer-valued icmp, but still an icmp "
                               "and not a pointer\n";
                  std::cout << "ERROR: not yet supported\n" ;
                  assert(0);
                }
              } else {
                uint64_t TypeSize = DL->getTypeStoreSizeInBits(A0->getType());
                int CallbackIdx = TypeSize == 8    ? 0
                                  : TypeSize == 16 ? 1
                                  : TypeSize == 32 ? 2
                                  : TypeSize == 64 ? 3
                                                   : 4;
                if (CallbackIdx == 4) {
                  std::cout << "UNKNOWNERROR";
                  std::cout << TypeSize << " is bit width\n";
                  std::cout << "ERROR: not yet supported\n" ;
                  assert(0);
                } else {
                  auto CallbackFunc = LogFunc[CallbackIdx];
                  assert(CallbackIdx >= 0);
                  assert(CallbackIdx <= 3);
                  auto Ty = Type::getIntNTy(C, TypeSize);
                  assert(is_signed >= 0);
                  assert(is_signed <= 1);
                  Value *ret_val = IRB.CreateCall(
                      CallbackFunc,
                      {ConstantInt::get(Int32Ty, cur_br_id),
                       br_inst->getCondition(), IRB.CreateIntCast(A0, Ty, true),
                       IRB.CreateIntCast(A1, Ty, true),
                       ConstantInt::get(Int8Ty, is_signed),
                       ConstantInt::get(Int8Ty, cond_type)});
                  br_inst->setCondition(ret_val);
                }
              }
            } else if (FCmpInst *cmp_inst =
                           dyn_cast<FCmpInst>(br_inst->getCondition())) {
              std::cout << "ERROR: not yet supported\n" ;
              assert(0);
            } else {
              std::cout << "ERROR" << br_inst->getCondition()->getName().str()
                        << " is not a ICMP nor FCMP but a conditional branch, "
                           "likely logical operators\n";
              std::cout << "@@@ edge id (" << cur_br_id << "," << br_id_1
                        << "), cond type non-ICMP \n";
              std::cout << "@@@ edge id (" << cur_br_id << "," << br_id_2
                        << "), cond type non-ICMP \n";
              std::cout << "ERROR: not yet supported\n" ;
              assert(0);
            }
          }
        } else if (auto *sw_inst = dyn_cast<SwitchInst>(&I)) {
            std::cout << "ERROR: not yet supported\n" ;
            assert(0);
        }
      }
    }
  }
  std::vector<Instruction *> deleteCalls;
  for (auto &F : M) {
    for (auto &BB : F) {
      for (auto &I : BB) {
        if (CallInst *call_inst = dyn_cast<CallInst>(&I)) {
          Function *fun = call_inst->getCalledFunction();
          if (fun && fun->getName().str() == "fake_func") {
            int count = 0;
            for (auto U : I.users()) {
              count++;
            }
            assert(count == 0);
            deleteCalls.emplace_back(&I);
          }
        }
      }
    }
  }

  for (auto I : deleteCalls) {
    I->eraseFromParent();
  }
  return true;
}

char SkeletonPass::ID = 0;

static void registerSkeletonPass(const PassManagerBuilder &,
                                 legacy::PassManagerBase &PM) {
  PM.add(new SkeletonPass());
}
static RegisterStandardPasses
    RegisterMyPass(PassManagerBuilder::EP_OptimizerLast, registerSkeletonPass);
static RegisterStandardPasses
    RegisterMyPass0(PassManagerBuilder::EP_EnabledOnOptLevel0,
                    registerSkeletonPass);
