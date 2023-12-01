init:
	git submodule update --init
	cd rocket-chip && git submodule update --init hardfloat cde

compile:
	mill -i CoupledL2.compile
	mill -i CoupledL2.test.compile

test-top-l2:
	mill -i CoupledL2.test.runMain coupledL2.TestTop_L2 -td build
	mv build/TestTop_L2.v build/TestTop.v

test-top-l2standalone:
	mill -i CoupledL2.test.runMain coupledL2.TestTop_L2_Standalone -td build
	mv build/TestTop_L2_Standalone.v build/TestTop.v

test-top-l2l3:
	mill -i CoupledL2.test.runMain coupledL2.TestTop_L2L3 -td build
	mv build/TestTop_L2L3.v build/TestTop.v

test-top-l2l3l2:
	mill -i CoupledL2.test.runMain coupledL2.TestTop_L2L3L2 -td build
	mv build/TestTop_L2L3L2.v build/TestTop.v

test-top-fullsys:
	mill -i CoupledL2.test.runMain coupledL2.TestTop_fullSys -td build | tee ./build/build.log
	mv build/TestTop_fullSys.v build/TestTop.v

test-top-fullsys_1:
	mill -i CoupledL2.test.runMain coupledL2.TestTop_fullSys_1 -td build
	mv build/TestTop_fullSys_1.v build/TestTop.v

test-top-l3:
	mill -i CoupledL2.test.runMain coupledL3.TestTop_L3 -td build
	mv build/TestTop_L3.v build/TestTop.v

test-top-for-l2-sysn:
	mill -i CoupledL2.test.runMain coupledL2.TestTop_l2_for_sysn -td build_l2
	mv build_l2/TestTop_l2_for_sysn.v build_l2/TestTop.v

test-top-for-l3-sysn:
	mill -i CoupledL2.test.runMain coupledL2.TestTop_L3_for_sysn -td build_l3
	mv build_l3/TestTop_L3_for_sysn.v build_l3/TestTop.v

clean:
	rm -rf ./build

bsp:
	mill -i mill.bsp.BSP/install

idea:
	mill -i mill.idea.GenIdea/idea

reformat:
	mill -i __.reformat

checkformat:
	mill -i __.checkFormat
