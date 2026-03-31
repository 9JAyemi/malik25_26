module calculator_sva (
    input logic signed [7:0] a,
    input logic signed [7:0] b,
    input logic op,
    input logic clk,
    input logic signed [7:0] result,
    input logic overflow
);

    // Result must match the selected arithmetic operation.
    check_result_matches_operation: assert property (
        @(posedge clk) disable iff (1'b0)
        result == (op ? (a - b) : (a + b))
    );

    // Overflow must be low when the previous cycle did not have an overflow condition.
    check_overflow_low_when_no_condition: assert property (
        @(posedge clk) disable iff (1'b0)
        (!$past((result[7] == 1 && op == 0 && a[7] == 1 && b[7] == 1) ||
                (result[7] == 1 && op == 1 && a[7] == 0 && b[7] == 1) ||
                (result[7] == 0 && op == 1 && a[7] == 1 && b[7] == 0))))
        |-> (overflow == 1'b0)
    );

    // Overflow must be high when the previous cycle had an overflow condition.
    check_overflow_high_when_condition: assert property (
        @(posedge clk) disable iff (1'b0)
        $past((result[7] == 1 && op == 0 && a[7] == 1 && b[7] == 1) ||
              (result[7] == 1 && op == 1 && a[7] == 0 && b[7] == 1) ||
              (result[7] == 0 && op == 1 && a[7] == 1 && b[7] == 0)))
        |-> (overflow == 1'b1)
    );

    // Overflow must be low on the first clock after reset deassertion.
    check_overflow_low_after_reset_release: assert property (
        @(posedge clk) disable iff (1'b0)
        $fell(1'b0) |-> (overflow == 1'b0)
    );

endmodule