module accumulator_sva #(
    parameter int unsigned n = 4
)(
    input logic clk,
    input logic [n-1:0] in,
    input logic [n:0] out
);

    // out equals the number of asserted input bits.
    check_out_matches_input_popcount: assert property (
        @(posedge clk) out == $countones(in)
    );

    // out never exceeds the number of inputs.
    check_out_within_valid_range: assert property (
        @(posedge clk) out <= n
    );

    // A zero input vector produces a zero output.
    check_zero_input_gives_zero_output: assert property (
        @(posedge clk) (in == '0) |-> (out == '0)
    );

    // A zero output implies no input bits are set.
    check_zero_output_implies_zero_input: assert property (
        @(posedge clk) (out == '0) |-> (in == '0)
    );

    // A one-hot input vector produces an output of one.
    check_onehot_input_gives_one: assert property (
        @(posedge clk) $onehot(in) |-> (out == 1)
    );

    // An all-ones input vector produces an output of n.
    check_all_ones_input_gives_n: assert property (
        @(posedge clk) (in == {n{1'b1}}) |-> (out == n)
    );

    // If the sampled input is unchanged, the sampled output is unchanged.
    check_stable_input_keeps_stable_output: assert property (
        @(posedge clk) !$initstate && (in == $past(in)) |-> (out == $past(out))
    );

endmodule