module calculator_sva (
    input logic signed [7:0] a,
    input logic signed [7:0] b,
    input logic op,
    input logic clk,
    input logic signed [7:0] result,
    input logic overflow
);

    // Addition mode drives result to a + b.
    check_add_result: assert property (
        @(posedge clk) disable iff (1'b0)
        (op == 1'b0) |-> (result == (a + b))
    );

    // Subtraction mode drives result to a - b.
    check_sub_result: assert property (
        @(posedge clk) disable iff (1'b0)
        (op == 1'b1) |-> (result == (a - b))
    );

    // Overflow is asserted for signed addition overflow.
    check_add_overflow_assert: assert property (
        @(posedge clk) disable iff (1'b0)
        ((op == 1'b0) &&
         (a[7] == 1 && b[7] == 1 && result[7] == 0)) |-> (overflow == 1'b1)
    );

    // Overflow is asserted for signed subtraction underflow.
    check_sub_underflow_assert: assert property (
        @(posedge clk) disable iff (1'b0)
        ((op == 1'b1) &&
         (a[7] == 0 && b[7] == 1 && result[7] == 1)) |-> (overflow == 1'b1)
    );

    // Overflow is asserted for signed subtraction overflow.
    check_sub_overflow_assert: assert property (
        @(posedge clk) disable iff (1'b0)
        ((op == 1'b1) &&
         (a[7] == 1 && b[7] == 0 && result[7] == 0)) |-> (overflow == 1'b1)
    );

    // Overflow is deasserted for all non-overflowing cases.
    check_no_overflow_assert: assert property (
        @(posedge clk) disable iff (1'b0)
        !((op == 1'b0) &&
          ((a[7] == 1 && b[7] == 1 && result[7] == 0) ||
           (a[7] == 0 && b[7] == 0 && result[7] == 1))) |-> (overflow == 1'b0)
    );

    // Overflow is deasserted for all non-underflowing cases.
    check_no_underflow_assert: assert property (
        @(posedge clk) disable iff (1'b0)
        !((op == 1'b1) &&
          ((a[7] == 0 && b[7] == 1 && result[7] == 1) ||
           (a[7] == 1 && b[7] == 0 && result[7] == 0))) |-> (overflow == 1'b0)
    );

    // Overflow can only be asserted for signed operations.
    check_overflow_signed_only: assert property (
        @(posedge clk) disable iff (1'b0)
        (overflow == 1'b1) |-> (a[7] == 1 || a[7] == 0 || b[7] == 1 || b[7] == 0)
    );

endmodule