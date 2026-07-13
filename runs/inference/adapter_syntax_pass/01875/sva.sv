module udp_mux_4to1_sva (
    input logic [3:0] out,
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel
);

    // out[0] selects in0[0] when sel[1] is low.
    check_out0_selects_in0_when_sel1_low: assert property (
        @($global_clock) (sel[1] == 1'b0) |-> (out[0] == in0[0])
    );

    // out[0] selects in1[0] when sel[1] is high.
    check_out0_selects_in1_when_sel1_high: assert property (
        @($global_clock) (sel[1] == 1'b1) |-> (out[0] == in1[0])
    );

    // out[1] selects in0[1] when sel[0] is low.
    check_out1_selects_in0_when_sel0_low: assert property (
        @($global_clock) (sel[0] == 1'b0) |-> (out[1] == in0[1])
    );

    // out[1] selects in1[1] when sel[0] is high.
    check_out1_selects_in1_when_sel0_high: assert property (
        @($global_clock) (sel[0] == 1'b1) |-> (out[1] == in1[1])
    );

    // out[2] selects in2[2] when sel[0] is low.
    check_out2_selects_in2_when_sel0_low: assert property (
        @($global_clock) (sel[0] == 1'b0) |-> (out[2] == in2[2])
    );

    // out[2] selects in3[2] when sel[0] is high.
    check_out2_selects_in3_when_sel0_high: assert property (
        @($global_clock) (sel[0] == 1'b1) |-> (out[2] == in3[2])
    );

    // out[3] selects in0[3] when sel[0] is low.
    check_out3_selects_in0_when_sel0_low: assert property (
        @($global_clock) (sel[0] == 1'b0) |-> (out[3] == in0[3])
    );

    // out[3] selects in1[3] when sel[0] is high.
    check_out3_selects_in1_when_sel0_high: assert property (
        @($global_clock) (sel[0] == 1'b1) |-> (out[3] == in1[3])
    );

endmodule