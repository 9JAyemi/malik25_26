module shift_add_sva (
    input logic        clk,
    input logic [15:0] a,
    input logic [15:0] y
);

    // y must equal a plus a shifted right by two.
    check_shift_add_function: assert property (
        @(posedge clk) y == (a + (a >> 2))
    );

    // Zero input must produce zero output.
    check_zero_input: assert property (
        @(posedge clk) (a == 16'h0000) |-> (y == 16'h0000)
    );

    // Inputs below four are unchanged because a>>2 is zero.
    check_small_input_identity: assert property (
        @(posedge clk) (a <= 16'd3) |-> (y == a)
    );

    // Up to 16'hCCCC, the 16-bit sum does not wrap and cannot be less than a.
    check_nonoverflow_region_ge_input: assert property (
        @(posedge clk) (a <= 16'hCCCC) |-> (y >= a)
    );

    // From 16'hCCCD upward, the 16-bit sum wraps and becomes less than a.
    check_overflow_region_lt_input: assert property (
        @(posedge clk) (a >= 16'hCCCD) |-> (y < a)
    );

    // The largest non-overflowing input produces all ones.
    check_max_nonoverflow_case: assert property (
        @(posedge clk) (a == 16'hCCCC) |-> (y == 16'hFFFF)
    );

    // The first overflowing input wraps the 16-bit result to zero.
    check_first_overflow_case: assert property (
        @(posedge clk) (a == 16'hCCCD) |-> (y == 16'h0000)
    );

endmodule