module top_module_sva (
    input logic clk,
    input logic reset,  // Synchronous active-high reset
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [11:0] s
);
    ///// Reset behavior /////
    // When reset is asserted, output must be zero.
    reset_clears_output: assert property (
        @(posedge clk) reset |-> (s == 12'b0)
    );

    ///// Functional mapping /////
    // When not in reset, s must equal zero-extended high byte of a*b.
    check_output_is_high_byte_of_product: assert property (
        @(posedge clk) disable iff (reset) s == {4'b0, (a*b)[15:8]}
    );

    // When not in reset, top 4 bits of s are always zero.
    check_top_nibble_zero: assert property (
        @(posedge clk) disable iff (reset) s[11:8] == 4'b0
    );

    ///// Temporal consistency /////
    // If high byte of a*b does not change, s must not change.
    stable_when_prod_hi_stable: assert property (
        @(posedge clk) disable iff (reset) ($past(!reset) && ((a*b)[15:8] == $past((a*b)[15:8]))) |-> (s == $past(s))
    );

    // If high byte of a*b changes, s must change.
    change_when_prod_hi_changes: assert property (
        @(posedge clk) disable iff (reset) ($past(!reset) && ((a*b)[15:8] != $past((a*b)[15:8]))) |-> (s != $past(s))
    );

    ///// Arithmetic implications /////
    // If either input is zero, output must be zero.
    zero_operand_implies_zero_output: assert property (
        @(posedge clk) disable iff (reset) ((a == 8'h00) || (b == 8'h00)) |-> (s == 12'h000)
    );

    // If either input is one, output must be zero (since high byte of product is zero).
    one_operand_implies_zero_output: assert property (
        @(posedge clk) disable iff (reset) ((a == 8'h01) || (b == 8'h01)) |-> (s == 12'h000)
    );

    // If product is less than 256, high byte is zero -> output must be zero.
    small_product_implies_zero_output: assert property (
        @(posedge clk) disable iff (reset) ((a*b) < 16'd256) |-> (s == 12'h000)
    );

    // If product is 256 or more, high byte is nonzero -> output must be nonzero.
    large_product_implies_nonzero_output: assert property (
        @(posedge clk) disable iff (reset) ((a*b) >= 16'd256) |-> (s != 12'h000)
    );
endmodule