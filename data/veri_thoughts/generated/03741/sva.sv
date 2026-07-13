module GreaterThan_sva (
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic       out
);

    wire [7:0] diff;
    assign diff = in1 - in2;

    // Output matches the OR-reduction of the subtraction result.
    check_out_matches_diff_or: assert property (
        @($global_clock) out == (|diff)
    );

    // Output is high exactly when the two inputs differ.
    check_out_matches_inequality: assert property (
        @($global_clock) out == (in1 != in2)
    );

    // Equal inputs produce a zero difference and a low output.
    check_equal_inputs_clear_out: assert property (
        @($global_clock) (in1 == in2) |-> (diff == 8'h00 && out == 1'b0)
    );

    // Unequal inputs produce a nonzero difference and a high output.
    check_unequal_inputs_set_out: assert property (
        @($global_clock) (in1 != in2) |-> (diff != 8'h00 && out == 1'b1)
    );

    // A zero internal difference forces the output low.
    check_zero_diff_means_out_low: assert property (
        @($global_clock) (diff == 8'h00) |-> (out == 1'b0)
    );

    // Any nonzero internal difference forces the output high.
    check_nonzero_diff_means_out_high: assert property (
        @($global_clock) (diff != 8'h00) |-> (out == 1'b1)
    );

    // A low output can only occur when the inputs are identical.
    check_out_low_only_on_equal_inputs: assert property (
        @($global_clock) (out == 1'b0) |-> (in1 == in2)
    );

    // A high output can only occur when the inputs are different.
    check_out_high_only_on_unequal_inputs: assert property (
        @($global_clock) (out == 1'b1) |-> (in1 != in2)
    );

endmodule