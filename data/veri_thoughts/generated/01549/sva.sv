module adder_sva (
    input logic CLK,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] sum,
    input logic overflow
);
    // Sum and overflow equal the 9-bit unsigned addition of a and b.
    check_sum_and_overflow_exact: assert property (
        @(posedge CLK) {overflow, sum} == ({1'b0, a} + {1'b0, b})
    );

    // If overflow is 1, the wrapped sum is less than operand a.
    check_overflow_implies_sum_lt_a: assert property (
        @(posedge CLK) overflow |-> (sum < a)
    );

    // If overflow is 1, the wrapped sum is less than operand b.
    check_overflow_implies_sum_lt_b: assert property (
        @(posedge CLK) overflow |-> (sum < b)
    );

    // If no overflow, sum is greater than or equal to operand a.
    check_no_overflow_ge_a: assert property (
        @(posedge CLK) !overflow |-> (sum >= a)
    );

    // If no overflow, sum is greater than or equal to operand b.
    check_no_overflow_ge_b: assert property (
        @(posedge CLK) !overflow |-> (sum >= b)
    );

    // Adding zero on b passes a through and no overflow.
    check_add_zero_b: assert property (
        @(posedge CLK) (b == 8'h00) |-> (sum == a) && (overflow == 1'b0)
    );

    // Adding zero on a passes b through and no overflow.
    check_add_zero_a: assert property (
        @(posedge CLK) (a == 8'h00) |-> (sum == b) && (overflow == 1'b0)
    );

    // 0xFF + 0x01 wraps to 0x00 with overflow.
    check_ff_plus_one: assert property (
        @(posedge CLK) (a == 8'hFF && b == 8'h01) |-> (sum == 8'h00) && (overflow == 1'b1)
    );

    // When a is 0xFF, sum equals b-1 (mod 256) and overflow when b != 0.
    check_ff_operand_a: assert property (
        @(posedge CLK) (a == 8'hFF) |-> (sum == (b - 8'h01)) && (overflow == (b != 8'h00))
    );

    // When b is 0xFF, sum equals a-1 (mod 256) and overflow when a != 0.
    check_ff_operand_b: assert property (
        @(posedge CLK) (b == 8'hFF) |-> (sum == (a - 8'h01)) && (overflow == (a != 8'h00))
    );
endmodule