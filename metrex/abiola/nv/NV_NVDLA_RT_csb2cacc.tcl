analyze -sv NV_NVDLA_RT_csb2cacc.v

elaborate -top NV_NVDLA_RT_csb2cacc

clock nvdla_core_clk
reset nvdla_core_rstn

# prdy is tied high by design
assert { csb2cacc_req_src_prdy == 1'b1 }

# Pipeline: csb2cacc_req_src_pvld should appear on csb2cacc_req_dst_pvld after 3 cycles
assert { csb2cacc_req_src_pvld |-> ##3 (csb2cacc_req_dst_pvld) }

# Pipeline data propagation: csb2cacc_req_src_pd should propagate to csb2cacc_req_dst_pd in 3 cycles
assert { csb2cacc_req_src_pvld & (csb2cacc_req_src_pd == csb2cacc_req_dst_pd) |-> ##3 (csb2cacc_req_dst_pd == csb2cacc_req_src_pd) }

# Response path: cacc2csb_resp_src_valid should appear on cacc2csb_resp_dst_valid after 3 cycles
assert { cacc2csb_resp_src_valid |-> ##3 (cacc2csb_resp_dst_valid) }

# On reset (active low) the pipeline valid registers are cleared
assert { !nvdla_core_rstn |-> (csb2cacc_req_pvld_d1 == 1'b0 && csb2cacc_req_pvld_d2 == 1'b0 && csb2cacc_req_pvld_d3 == 1'b0 && cacc2csb_resp_valid_d1 == 1'b0 && cacc2csb_resp_valid_d2 == 1'b0 && cacc2csb_resp_valid_d3 == 1'b0) }

# Set prover options
set_prove_time_limit 3600
set_engine_mode Tri
prove -all
