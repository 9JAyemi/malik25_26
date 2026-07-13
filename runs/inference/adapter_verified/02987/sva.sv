module calculator_sva (
    input logic signed [7:0] a,
    input logic signed [7:0] b,
    input logic op,
    input logic clk,
    input logic signed [7:0] result,
    input logic overflow
);

// Result equals the selected operation (add/sub) when sampled on clk.
    check_result_function: assert property (
        @(posedge clk) result == (op ? (a - b) : (a + b))
    );

// Overflow is 0 on the next clock when the RTL does not detect an overflow condition.
    check_overflow_clear_when_no_overflow: assert property (
        @(posedge clk) disable iff (1'b0)
            !((result[7] == 1 && op == 1'b0 && a[7] == 1'b1 && b[7] == 1'b1) ||
              (result[7] == 1'b1 && op == 1'b1 && a[7] == 1'b0 && b[7] == 1'b1) ||
              (result[7] == 1'b0 && op == 1'b1 && a[7] == 1'b1 && b[7] == 1'b0))
            |=> (overflow == 1'b0)
    );

// Overflow is 1 on the next clock when the RTL detects an overflow condition.
    check_overflow_set_when_overflow: assert property (
        @(posedge clk) disable iff (1'b0)
            ((result[7] == 1 && op == 1'b0 && a[7] == 1'b1 && b[7] == 1'b1) ||
             (result[7] == 1'b1 && op == 1'b1 && a[7] == 1'b0 && b[7] == 1'b1) ||
             (result[7] == 1'b0 && op == 1'b1 && a[7] == 1'b1 && b[7] == 1'b0))
            |=> (overflow == 1'b1)
    );

// Overflow is 0 on the next clock after a previous overflow indication.
    check_overflow_clear_after_previous_overflow: assert property (
        @(posedge clk) disable iff (1'b0)
            $past(overflow) |=> (overflow == 1'b0)
    );

// Overflow is 0 on the next clock after a previous non-overflow indication.
    check_overflow_clear_after_previous_no_overflow: assert property (
        @(posedge clk) disable iff (1'b0)
            !$past(overflow) |=> (overflow == 1'b0)
    );

endmodule
