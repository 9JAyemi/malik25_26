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

    // o_wk3_7 selects the upper byte from i_mk15to12 when i_op and i_wf_post_pre differ.
    check_wk3_7_selects_upper_when_op_differs: assert property (
        @($global_clock) (i_op ^ i_wf_post_pre) |-> (o_wk3_7 == i_mk15to12[31:24])
    );

    // o_wk3_7 selects the upper byte from i_mk3to0 when i_op and i_wf_post_pre match.
    check_wk3_7_selects_lower_when_op_matches: assert property (
        @($global_clock) !(i_op ^ i_wf_post_pre) |-> (o_wk3_7 == i_mk3to0[31:24])
    );

    // o_wk2_6 selects the next byte from i_mk15to12 when i_op and i_wf_post_pre differ.
    check_wk2_6_selects_upper_when_op_differs: assert property (
        @($global_clock) (i_op ^ i_wf_post_pre) |-> (o_wk2_6 == i_mk15to12[23:16])
    );

    // o_wk2_6 selects the next byte from i_mk3to0 when i_op and i_wf_post_pre match.
    check_wk2_6_selects_lower_when_op_matches: assert property (
        @($global_clock) !(i_op ^ i_wf_post_pre) |-> (o_wk2_6 == i_mk3to0[23:16])
    );

    // o_wk1_5 selects the middle byte from i_mk15to12 when i_op and i_wf_post_pre differ.
    check_wk1_5_selects_upper_when_op_differs: assert property (
        @($global_clock) (i_op ^ i_wf_post_pre) |-> (o_wk1_5 == i_mk15to12[15:8])
    );

    // o_wk1_5 selects the middle byte from i_mk3to0 when i_op and i_wf_post_pre match.
    check_wk1_5_selects_lower_when_op_matches: assert property (
        @($global_clock) !(i_op ^ i_wf_post_pre) |-> (o_wk1_5 == i_mk3to0[15:8])
    );

    // o_wk0_4 selects the lower byte from i_mk15to12 when i_op and i_wf_post_pre differ.
    check_wk0_4_selects_upper_when_op_differs: assert property (
        @($global_clock) (i_op ^ i_wf_post_pre) |-> (o_wk0_4 == i_mk15to12[7:0])
    );

    // o_wk0_4 selects the lower byte from i_mk3to0 when i_op and i_wf_post_pre match.
    check_wk0_4_selects_lower_when_op_matches: assert property (
        @($global_clock) !(i_op ^ i_wf_post_pre) |-> (o_wk0_4 == i_mk3to0[7:0])
    );

endmodule