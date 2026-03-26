module max_finder_sva (
    input logic        clk,
    input logic [15:0] D,
    input logic [15:0] max
);

    // max must equal D shifted right by the upper nibble of D.
    check_output_matches_shift_rule: assert property (
        @(posedge clk) max == (D >> D[15:12])
    );

    // When the upper nibble is zero, max must pass D through unchanged.
    check_passthrough_when_shift_zero: assert property (
        @(posedge clk) (D[15:12] == 4'h0) |-> (max == D)
    );

    // A zero input must produce a zero output.
    check_zero_input_produces_zero: assert property (
        @(posedge clk) (D == 16'h0000) |-> (max == 16'h0000)
    );

    // When the shift amount is fifteen, only the original MSB can remain.
    check_max_shift_case: assert property (
        @(posedge clk) (D[15:12] == 4'hF) |-> (max == {15'b0, D[15]})
    );

    // Right shifting cannot increase the unsigned value.
    check_output_not_greater_than_input: assert property (
        @(posedge clk) max <= D
    );

    // Any nonzero shift must clear the output MSB.
    check_msb_clears_on_nonzero_shift: assert property (
        @(posedge clk) (D[15:12] != 4'h0) |-> (max[15] == 1'b0)
    );

endmodule