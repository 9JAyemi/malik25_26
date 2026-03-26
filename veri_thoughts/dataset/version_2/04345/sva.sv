module inc_sva (
    input logic [3:0] i,
    input logic [3:0] inc_val,
    input logic [3:0] o
);

    // Output is always the 4-bit sum of the inputs.
    check_sum_matches_inputs: assert property (
        @($global_clock) o == (i + inc_val)
    );

    // A zero increment leaves the input unchanged.
    check_zero_increment_passthrough: assert property (
        @($global_clock) (inc_val == 4'h0) |-> (o == i)
    );

    // A zero input passes the increment value through.
    check_zero_input_passthrough: assert property (
        @($global_clock) (i == 4'h0) |-> (o == inc_val)
    );

    // Adding one to 4'hF wraps around to 4'h0.
    check_full_plus_one_wraps: assert property (
        @($global_clock) ((i == 4'hF) && (inc_val == 4'h1)) |-> (o == 4'h0)
    );

endmodule