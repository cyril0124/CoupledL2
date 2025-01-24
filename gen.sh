#!/bin/bash

set -e

# RELEASE_RTL=1 make test-top-ut
RELEASE_RTL=1 MMIOBRIDGE_TOP=1 make test-top-ut

rtl_dir=$(pwd)/build/TestTop
gen_dir=$(pwd)/gen
mkdir -p $gen_dir

cp $rtl_dir/*.v $gen_dir
rm $gen_dir/ClockGate.v

cp $(pwd)/xs-issue-b-difftest-verilog/rtl $gen_dir -r

# Replace
sed -i 's/TL2CHICoupledL2/bosc_TL2CHICoupledL2/g' $gen_dir/TestTop.v

# Delete
sed -i '/\.io_hartId(l2_nodes_io_hartId),/d' $gen_dir/TestTop.v
sed -i '/\.io_pfCtrlFromCore_.*/d' $gen_dir/TestTop.v
sed -i '/\.io_debugTopDown_.*/d' $gen_dir/TestTop.v
sed -i '/\.io_l2_hint_bits_isGrantData.*/d' $gen_dir/TestTop.v
sed -i '/\.io_l2_tlb_req_req_ready.*/d' $gen_dir/TestTop.v
sed -i '/\.io_l2_tlb_req_req_kill.*/d' $gen_dir/TestTop.v
sed -i '/\.io_l2_tlb_req_req_bits_isPrefetch.*/d' $gen_dir/TestTop.v
sed -i '/\.io_l2_tlb_req_req_bits_size.*/d' $gen_dir/TestTop.v
sed -i '/\.io_l2_tlb_req_resp_ready.*/d' $gen_dir/TestTop.v
sed -i '/\.io_l2_tlb_req_resp_bits_paddr_0.*/d' $gen_dir/TestTop.v
sed -i '/\.io_l2_tlb_req_resp_bits_excp_0_gpf_st.*/d' $gen_dir/TestTop.v
sed -i '/\.io_l2_tlb_req_resp_bits_excp_0_gpf_instr.*/d' $gen_dir/TestTop.v
sed -i '/\.io_l2_tlb_req_resp_bits_excp_0_pf_st.*/d' $gen_dir/TestTop.v
sed -i '/\.io_l2_tlb_req_resp_bits_excp_0_pf_instr.*/d' $gen_dir/TestTop.v
sed -i '/\.io_l2_tlb_req_resp_bits_excp_0_af_st.*/d' $gen_dir/TestTop.v
sed -i '/\.io_l2_tlb_req_resp_bits_excp_0_af_instr.*/d' $gen_dir/TestTop.v
sed -i '/\.io_l2_tlb_req_pmp_resp_st.*/d' $gen_dir/TestTop.v
sed -i '/\.io_l2_tlb_req_pmp_resp_instr.*/d' $gen_dir/TestTop.v
sed -i '/\.io_l2_tlb_req_pmp_resp_atomic.*/d' $gen_dir/TestTop.v


# Append
sed -i '/\.auto_in_0_a_bits_echo_isKeyword(l2_nodes_auto_in_0_a_bits_echo_isKeyword),/a .auto_in_0_a_bits_user_reqSource(0),' $gen_dir/TestTop.v
sed -i '/\.auto_in_1_a_bits_echo_isKeyword(l2_nodes_auto_in_1_a_bits_echo_isKeyword),/a .auto_in_1_a_bits_user_reqSource(0),' $gen_dir/TestTop.v
sed -i '/\.auto_in_2_a_bits_echo_isKeyword(l2_nodes_auto_in_2_a_bits_echo_isKeyword),/a .auto_in_2_a_bits_user_reqSource(0),' $gen_dir/TestTop.v
sed -i '/\.auto_in_3_a_bits_echo_isKeyword(l2_nodes_auto_in_3_a_bits_echo_isKeyword),/a .auto_in_3_a_bits_user_reqSource(0),' $gen_dir/TestTop.v

