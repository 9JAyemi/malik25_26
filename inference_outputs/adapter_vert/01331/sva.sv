property ClockSynceotid; @(posedge clk_in_14) (i_op) != (i_wf_post_pre) |->  (o_wk3_7 == i_mk15to12[31:24]) && (o_wk2_6 == i_mk15to12[23:16]) && (o_wk1_5 == i_mk15to12[15:8]) && (o_wk0_4 == i_mk15to12[7:0]); endproperty 
 
 property ClockSynceotid; @(posedge clk_in_14) (i_op) == (i_wf_post_pre) |->  (o_wk3_7 == i_mk3to0[31:24]) && (o_wk2_6 == i_mk3to0[23:16]) && (o_wk1_5 == i_mk3to0[15:8]) && (o_wk0_4 == i_mk3to0[7:0]); endproperty 
 