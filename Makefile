all:
	@echo "make [clean, build, noMonteCarloExecution, monteCarloExecution, noisyBinarySearch]"

clean:
	rm -rf onebyte_test build *.o

build:
	mkdir -p build && cd build && cmake .. && make
	clang-11 -c runtime_func.c -g3 -O0 -o runtime_func.o
	clang-11 -Xclang -load -Xclang build/skeleton/libSkeletonPass.so -g3 -O0 onebyte_test.c runtime_func.o -o onebyte_test -lm

noMonteCarloExecution:
	COLLECT_COUNT=1 ./onebyte_test onebyte.txt

monteCarloExecution:
	MONTECARLO_EXE=onebyte.policy COLLECT_COUNT=1 ./onebyte_test onebyte.txt

noisyBinarySearch:
	INPUT_FILE=onebyte.txt MONTECARLO_EXE=onebyte.policy COLLECT_COUNT=1 NOISY_BINARY_SEARCH=1 ./onebyte_test onebyte.txt
