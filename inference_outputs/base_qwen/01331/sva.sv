```systemverilog
module wkg_sva (
    input logic CLK,
    input logic RESETn,
    input logic i_op,
    input logic i_wf_post_pre,
    input logic [31:0] i_mk3to0,
    input logic [31:0] i_mk15to12,
    output logic [7:0] o_wk3_7,
    output logic [7:0] o_wk2_6,
    output logic [7:0] o_wk1_5,
    output logic [7:0] o_wk0_4
);
    // Combinational logic: o_wk3_7, o_wk2_6, o_wk1_5, o_wk0_4 are determined by i_op and i_wf_post_pre
    // Ensure that o_wk3_7, o_wk2_6, o_wk1_5, o_wk0_4 are correctly assigned based on i_op and i_wf_post_pre
    comb_logic: assert property (
        @(posedge CLK) disable iff (!RESETn) (o_wk3_7 == (i_op ^ i_wf_post_pre) ? i_mk15to12[31:24] : i_mk3to0[31:24]) &&
                                             (o_wk2_6 == (i_op ^ i_wf_post_pre) ? i_mk15to12[23:16] : i_mk3to0[23:16]) &&
                                             (o_wk1_5 == (i_op ^ i_wf_post_pre) ? i_mk15to12[15:8]  : i_mk3to0[15:8]) &&
                                             (o_wk0_4 == (i_op ^ i_wf_post_pre) ? i_mk15to12[7:0]   : i_mk3to0[7:0])
    );
endmodule
```