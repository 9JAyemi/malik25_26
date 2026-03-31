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

    // No RTL clock or reset; sample combinational behavior on the formal global clock.

    // o_wk3_7 selects the upper byte from the selected input word.
    check_o_wk3_7_mux: assert property (
        @($global_clock)
        o_wk3_7 == ((i_op ^ i_wf_post_pre) ? i_mk3to0[31:24] : i_mk15to12[31:24])
    );

    // o_wk2_6 selects the middle byte from the selected input word.
    check_o_wk2_6_mux: assert property (
        @($global_clock)
        o_wk2_6 == ((i_op ^ i_wf_post_pre) ? i_mk3to0[23:16] : i_mk15to12[23:16])
    );

    // o_wk1_5 selects the lower byte from the selected input word.
    check_o_wk1_5_mux: assert property (
        @($global_clock)
        o_wk1_5 == ((i_op ^ i_wf_post_pre) ? i_mk3to0[15:8] : i_mk15to12[15:8])
    );

    // o_wk0_4 selects the least-significant byte from the selected input word.
    check_o_wk0_4_mux: assert property (
        @($global_clock)
        o_wk0_4 == ((i_op ^ i_wf_post_pre) ? i_mk3to0[7:0] : i_mk15to12[7:0])
    );

    // When i_op and i_wf_post_pre differ, the upper byte comes from i_mk3to0.
    check_upper_byte_selects_mk3to0: assert property (
        @($global_clock)
        (i_op ^ i_wf_post_pre) |-> (o_wk3_7 == i_mk3to0[31:24] &&
                                   o_wk2_6 == i_mk3to0[23:16] &&
                                   o_wk1_5 == i_mk3to0[15:8] &&
                                   o_wk0_4 == i_mk3to0[7:0])
    );

    // When i_op and i_wf_post_pre are equal, the upper byte comes from i_mk15to12.
    check_upper_byte_selects_mk15to12: assert property (
        @($global_clock)
        !(i_op ^ i_wf_post_pre) |-> (o_wk3_7 == i_mk15to12[31:24] &&
                                    o_wk2_6 == i_mk15to12[23:16] &&
                                    o_wk1_5 == i_mk15to12[15:8] &&
                                    o_wk0_4 == i_mk15to12[7:0])
    );

endmodule