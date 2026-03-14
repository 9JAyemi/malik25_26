module fibonacci_sva (
    input logic clk,
    input logic reset,
    input logic [31:0] fib_num
);
    ///// Reset behavior /////
    // When reset is asserted, fib_num must be 0 by the next cycle.
    reset_clears_by_next: assert property (
        @(posedge clk) reset |=> (fib_num == 32'd0)
    );

    // If reset is held high across consecutive cycles, fib_num is 0.
    reset_held_forces_zero: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (fib_num == 32'd0)
    );

    ///// Sequential update rules /////
    // If fib_num is 0 (and not in reset), next value must be 1.
    update_from_zero: assert property (
        @(posedge clk) disable iff (reset) (fib_num == 32'd0) |=> (fib_num == 32'd1)
    );

    // If fib_num is non-zero (and not in reset), next value must be fib + (fib - 1).
    update_from_nonzero: assert property (
        @(posedge clk) disable iff (reset) (fib_num != 32'd0) |=> (fib_num == $past(fib_num) + ($past(fib_num) - 32'd1))
    );

    ///// Steady-state behavior /////
    // Once fib_num reaches 1 (without reset), it remains 1.
    one_is_stable: assert property (
        @(posedge clk) disable iff (reset) (fib_num == 32'd1) |=> (fib_num == 32'd1)
    );

    ///// Arithmetic characteristics /////
    // From any non-zero value (without reset), the next value is always odd.
    next_odd_from_nonzero: assert property (
        @(posedge clk) disable iff (reset) (fib_num != 32'd0) |=> (fib_num[0] == 1'b1)
    );
endmodule