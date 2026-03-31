module WKG_sva (
    input logic        i_op,
    input logic        i_wf_post_pre,
    input logic [31:0] i_mk3to0,
    input logic [31:0] i_mk15to12,
    input logic [7:0]  o_wk3_7,
    input logic [7:0]  o_wk2_6,
    input logic [7:0]  o_wk1_5,
    input logic [7:0]  o_wk0_4
);
    // No clock/reset in RTL; sample assertions on posedge of i_op.
    logic w_out_sel;
    assign w_out_sel = i_op ^ i_wf_post_pre;

    // When select=0, concatenated outputs equal i_mk15to12.
    check_concat_sel0: assert property (
        @(posedge i_op) (!w_out_sel) |-> ({o_wk3_7, o_wk2_6, o_wk1_5, o_wk0_4} == i_mk15to12)
    );

    // When select=1, concatenated outputs equal i_mk3to0.
    check_concat_sel1: assert property (
        @(posedge i_op) (w_out_sel) |-> ({o_wk3_7, o_wk2_6, o_wk1_5, o_wk0_4} == i_mk3to0)
    );

    // When select=0, o_wk3_7 maps to i_mk15to12[31:24].
    check_sel0_byte_31_24: assert property (
        @(posedge i_op) (!w_out_sel) |-> (o_wk3_7 == i_mk15to12[31:24])
    );

    // When select=0, o_wk2_6 maps to i_mk15to12[23:16].
    check_sel0_byte_23_16: assert property (
        @(posedge i_op) (!w_out_sel) |-> (o_wk2_6 == i_mk15to12[23:16])
    );

    // When select=0, o_wk1_5 maps to i_mk15to12[15:8].
    check_sel0_byte_15_8: assert property (
        @(posedge i_op) (!w_out_sel) |-> (o_wk1_5 == i_mk15to12[15:8])
    );

    // When select=0, o_wk0_4 maps to i_mk15to12[7:0].
    check_sel0_byte_7_0: assert property (
        @(posedge i_op) (!w_out_sel) |-> (o_wk0_4 == i_mk15to12[7:0])
    );

    // When select=1, o_wk3_7 maps to i_mk3to0[31:24].
    check_sel1_byte_31_24: assert property (
        @(posedge i_op) (w_out_sel) |-> (o_wk3_7 == i_mk3to0[31:24])
    );

    // When select=1, o_wk2_6 maps to i_mk3to0[23:16].
    check_sel1_byte_23_16: assert property (
        @(posedge i_op) (w_out_sel) |-> (o_wk2_6 == i_mk3to0[23:16])
    );

    // When select=1, o_wk1_5 maps to i_mk3to0[15:8].
    check_sel1_byte_15_8: assert property (
        @(posedge i_op) (w_out_sel) |-> (o_wk1_5 == i_mk3to0[15:8])
    );

    // When select=1, o_wk0_4 maps to i_mk3to0[7:0].
    check_sel1_byte_7_0: assert property (
        @(posedge i_op) (w_out_sel) |-> (o_wk0_4 == i_mk3to0[7:0])
    );

endmodule