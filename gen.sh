#!/bin/bash

# set -e

RELEASE_RTL=1 make test-top-ut-release
# RELEASE_RTL=1 MMIOBRIDGE_TOP=1 make test-top-ut

rtl_dir=$(pwd)/build/release/TestTop
gen_dir=$(pwd)/gen
top_file=$gen_dir/TestTop.sv
mkdir -p $gen_dir

cp $rtl_dir/*.sv $gen_dir
cp $rtl_dir/*.v $gen_dir
rm $gen_dir/ClockGate.sv

set -e

cp $(pwd)/xs-issue-e-b-difftest-verilog/rtl $gen_dir -r

# Replace
sed -i 's/TL2CHICoupledL2/bosc_TL2CHICoupledL2/g' $top_file

# Delete
sed -i '/\.io_hartId.*\(.*\),/d' $top_file
sed -i '/\.io_pfCtrlFromCore_.*/d' $top_file
sed -i '/\.io_debugTopDown_.*/d' $top_file
# sed -i '/\.io_l2_hint_bits_isGrantData.*/d' $top_file
sed -i '/\.io_l2_tlb_req_req_ready.*/d' $top_file
sed -i '/\.io_l2_tlb_req_req_kill.*/d' $top_file
sed -i '/\.io_l2_tlb_req_req_bits_isPrefetch.*/d' $top_file
sed -i '/\.io_l2_tlb_req_req_bits_size.*/d' $top_file
sed -i '/\.io_l2_tlb_req_resp_ready.*/d' $top_file
sed -i '/\.io_l2_tlb_req_resp_bits_paddr_0.*/d' $top_file
sed -i '/\.io_l2_tlb_req_resp_bits_excp_0_gpf_st.*/d' $top_file
sed -i '/\.io_l2_tlb_req_resp_bits_excp_0_gpf_instr.*/d' $top_file
sed -i '/\.io_l2_tlb_req_resp_bits_excp_0_pf_st.*/d' $top_file
sed -i '/\.io_l2_tlb_req_resp_bits_excp_0_pf_instr.*/d' $top_file
sed -i '/\.io_l2_tlb_req_resp_bits_excp_0_af_st.*/d' $top_file
sed -i '/\.io_l2_tlb_req_resp_bits_excp_0_af_instr.*/d' $top_file
sed -i '/\.io_l2_tlb_req_pmp_resp_st.*/d' $top_file
sed -i '/\.io_l2_tlb_req_pmp_resp_instr.*/d' $top_file
sed -i '/\.io_l2_tlb_req_pmp_resp_atomic.*/d' $top_file

# Append
sed -i '/\.auto_in_0_a_bits_echo_isKeyword(l2_nodes_auto_in_0_a_bits_echo_isKeyword),/a .auto_in_0_a_bits_user_reqSource(0),' $top_file
sed -i '/\.auto_in_1_a_bits_echo_isKeyword(l2_nodes_auto_in_1_a_bits_echo_isKeyword),/a .auto_in_1_a_bits_user_reqSource(0),' $top_file
sed -i '/\.auto_in_2_a_bits_echo_isKeyword(l2_nodes_auto_in_2_a_bits_echo_isKeyword),/a .auto_in_2_a_bits_user_reqSource(0),' $top_file
sed -i '/\.auto_in_3_a_bits_echo_isKeyword(l2_nodes_auto_in_3_a_bits_echo_isKeyword),/a .auto_in_3_a_bits_user_reqSource(0),' $top_file

echo "gen.sh Finish"