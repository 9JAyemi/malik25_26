module top_module_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [3:0] counter_out,
    input logic [15:0] adder_sum,
    input logic overflow,
    input logic [15:0] final_output
);

// Counter increments by one on the next cycle when enabled and not in reset.
    check_counter_increments: assert property (
        @(posedge clk) disable iff (reset) enable |=> (counter_out == ($past(counter_out) + 4'd1))
    );

// Counter holds its value on the next cycle when not enabled and not in reset.
    check_counter_holds: assert property (
        @(posedge clk) disable iff (reset) !enable |=> (counter_out == $past(counter_out))
    );

// Counter clears to zero on the next cycle when reset is asserted.
    check_counter_resets: assert property (
        @(posedge clk) reset |=> (counter_out == 4'd0)
    );

// Adder sum is the 16-bit sum of A and B.
    check_adder_sum: assert property (
        @(posedge clk) adder_sum == (A + B)
    );

// Overflow matches the RTL carry-out equation.
    check_overflow_equation: assert property (
        @(posedge clk) overflow == ((A[15] & B[15] & ~adder_sum[15]) | (~A[15] & ~B[15] & adder_sum[15]))
    );

// Overflow is high exactly when the 16-bit addition overflows.
    check_overflow_matches_addition: assert property (
        @(posedge clk) overflow == ((A[15] & B[15]) | (~A[15] & ~B[15]))
    );

// Final output selects counter_out when it is greater than adder_sum.
    check_final_output_selects_counter: assert property (
        @(posedge clk) (counter_out > adder_sum) |-> (final_output == counter_out)
    );

// Final output selects adder_sum when it is greater than or equal to counter_out.
    check_final_output_selects_adder: assert property (
        @(posedge clk) (counter_out <= adder_sum) |-> (final_output == adder_sum)
    );

endmodule
