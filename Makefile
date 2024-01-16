define append_log_and_status
	@echo -e "/*" > temp.txt
	@git log -1 >> temp.txt
	@echo -e "*/\n" >> temp.txt

	@echo -e "/*" >> temp.txt
	@git status >> temp.txt
	@echo -e "*/\n" >> temp.txt

	@cat temp.txt  build/TestTop.v > temp_1 && mv temp_1 build/TestTop.v
	@rm temp.txt
endef

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
	$(call append_log_and_status)

test-top-fullsys-4Core:
	mill -i CoupledL2.test.runMain coupledL2.TestTop_fullSys_4Core -td build | tee ./build/build.log
	mv build/TestTop_fullSys_4Core.v build/TestTop.v
	$(call append_log_and_status)

test-top-fullsys-1Core:
	mill -i CoupledL2.test.runMain coupledL2.TestTop_fullSys_1Core -td build | tee ./build/build.log
	mv build/TestTop_fullSys_1Core.v build/TestTop.v
	$(call append_log_and_status)


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
