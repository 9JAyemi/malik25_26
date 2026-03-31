module binary_multiplier_sva (
    input logic CLK,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [15:0] result
);
    // RTL has no clock/reset; purely combinational; assertions use external CLK.

    // Result equals zero-extended product of a and b (lower 16 bits of 16x16 product).
    check_result_matches_product: assert property (
        @(posedge CLK) disable iff (1'b0) result == (({8'b0, a} * {8'b0, b})[15:0])
    );

    // If a is zero, result is zero.
    check_zero_a_yields_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (a == 8'd0) |-> (result == 16'd0)
    );

    // If b is zero, result is zero.
    check_zero_b_yields_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (b == 8'd0) |-> (result == 16'd0)
    );

    // Zero result implies one operand is zero.
    check_zero_result_implies_zero_operand: assert property (
        @(posedge CLK) disable iff (1'b0) (result == 16'd0) |-> ((a == 8'd0) || (b == 8'd0))
    );

    // If a is one, result equals zero-extended b.
    check_one_a: assert property (
        @(posedge CLK) disable iff (1'b0) (a == 8'd1) |-> (result == {8'b0, b})
    );

    // If b is one, result equals zero-extended a.
    check_one_b: assert property (
        @(posedge CLK) disable iff (1'b0) (b == 8'd1) |-> (result == {8'b0, a})
    );

    // If a is two, result equals b shifted left by 1 (zero-extended).
    check_two_a: assert property (
        @(posedge CLK) disable iff (1'b0) (a == 8'd2) |-> (result == ({8'b0, b} << 1))
    );

    // If b is two, result equals a shifted left by 1 (zero-extended).
    check_two_b: assert property (
        @(posedge CLK) disable iff (1'b0) (b == 8'd2) |-> (result == ({8'b0, a} << 1))
    );

    // Result never exceeds 255*255 = 16'hFE01.
    check_result_upper_bound: assert property (
        @(posedge CLK) disable iff (1'b0) result <= 16'hFE01
    );

    // Commutativity: same result if operands are swapped (lower 16 bits).
    check_commutative_product: assert property (
        @(posedge CLK) disable iff (1'b0) result == (({8'b0, b} * {8'b0, a})[15:0])
    );

    // Specific corner: 0xFF * 0xFF = 16'hFE01.
    check_ff_times_ff: assert property (
        @(posedge CLK) disable iff (1'b0) ((a == 8'hFF) && (b == 8'hFF)) |-> (result == 16'hFE01)
    );

endmodule