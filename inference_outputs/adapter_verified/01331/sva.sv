module WKG_sva (
    input logic        clk,
    input logic        i_op,
    input logic        i_wf_post_pre,
    input logic [31:0] i_mk3to0,
    input logic [31:0] i_mk15to12,
    input logic [7:0]  o_wk3_7,
    input logic [7:0]  o_wk2_6,
    input logic [7:0]  o_wk1_5,
    input logic [7:0]  o_wk0_4
);

// o_wk3_7 selects i_mk15to12[31:24] when i_op == i_wf_post_pre.
    check_wk3_7_selects_15to12_when_op_eq_postpre: assert property (
        @(posedge clk) (i_op == i_wf_post_pre) |-> (o_wk3_7 == i_mk15to12[31:24])
    );

// o_wk3_7 selects i_mk3to0[31:24] when i_op != i_wf_post_pre.
    check_wk3_7_selects_3to0_when_op_ne_postpre: assert property (
        @(posedge clk) (i_op != i_wf_post_pre) |-> (o_wk3_7 == i_mk3to0[31:24])
    );

// o_wk2_6 selects i_mk15to12[23:16] when i_op == i_wf_post_pre.
    check_wk2_6_selects_15to12_when_op_eq_postpre: assert property (
        @(posedge clk) (i_op == i_wf_post_pre) |-> (o_wk2_6 == i_mk15to12[23:16])
    );

// o_wk2_6 selects i_mk3to0[23:16] when i_op != i_wf_post_pre.
    check_wk2_6_selects_3to0_when_op_ne_postpre: assert property (
        @(posedge clk) (i_op != i_wf_post_pre) |-> (o_wk2_6 == i_mk3to0[23:16])
    );

// o_wk1_5 selects i_mk15to12[15:8] when i_op == i_wf_post_pre.
    check_wk1_5_selects_15to12_when_op_eq_postpre: assert property (
        @(posedge clk) (i_op == i_wf_post_pre) |-> (o_wk1_5 == i_mk15to12[15:8])
    );

// o_wk1_5 selects i_mk3to0[15:8] when i_op != i_wf_post_pre.
    check_wk1_5_selects_3to0_when_op_ne_postpre: assert property (
        @(posedge clk) (i_op != i_wf_post_pre) |-> (o_wk1_5 == i_mk3to0[15:8])
    );

// o_wk0_4 selects i_mk15to12[7:0] when i_op == i_wf_post_pre.
    check_wk0_4_selects_15to12_when_op_eq_postpre: assert property (
        @(posedge clk) (i_op == i_wf_post_pre) |-> (o_wk0_4 == i_mk15to12[7:0])
    );

// o_wk0_4 selects i_mk3to0[7:0] when i_op != i_wf_post_pre.
    check_wk0_4_selects_3to0_when_op_ne_postpre: assert property (
        @(posedge clk) (i_op != i_wf_post_pre) |-> (o_wk0_4 == i_mk3to0[7:0])
    );

endmodule
