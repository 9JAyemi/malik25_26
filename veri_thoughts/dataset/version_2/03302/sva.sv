module DEMUX_sva (
    input logic clk,
    input logic in,
    input logic out0,
    input logic out1,
    input logic out2,
    input logic out3
);

    // out0 is driven as the inverse of the input.
    check_out0_inverse_of_in: assert property (
        @(posedge clk) out0 == ~in
    );

    // out3 directly follows the input.
    check_out3_matches_in: assert property (
        @(posedge clk) out3 == in
    );

    // out1 is always low.
    check_out1_constant_low: assert property (
        @(posedge clk) out1 == 1'b0
    );

    // out2 is always low.
    check_out2_constant_low: assert property (
        @(posedge clk) out2 == 1'b0
    );

    // Exactly one output is high on every sampled cycle.
    check_outputs_onehot: assert property (
        @(posedge clk) $onehot({out0, out1, out2, out3})
    );

    // A low input selects only out0.
    check_input_low_selects_out0: assert property (
        @(posedge clk) (in == 1'b0) |-> (out0 && !out1 && !out2 && !out3)
    );

    // A high input selects only out3.
    check_input_high_selects_out3: assert property (
        @(posedge clk) (in == 1'b1) |-> (!out0 && !out1 && !out2 && out3)
    );

endmodule