module and_gate_sva (
    input logic A,
    input logic B,
    input logic clk,
    input logic reset,
    input logic X
);

// X is 0 on the cycle after reset is asserted.
    check_reset_clears_x: assert property (
        @(posedge clk) reset |=> (X == 1'b0)
    );

// X is 0 on the cycle after reset is deasserted.
    check_reset_release_clears_x: assert property (
        @(posedge clk) reset ##1 !reset |=> (X == 1'b0)
    );

// When not in reset, X equals the previous cycle's A & B.
    check_and_update: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (X == ($past(A) & $past(B)))
    );

// When not in reset and A is 0, X becomes 0 on the next cycle.
    check_zero_when_a_zero: assert property (
        @(posedge clk) disable iff (reset) (A == 1'b0) |=> (X == 1'b0)
    );

// When not in reset and B is 0, X becomes 0 on the next cycle.
    check_zero_when_b_zero: assert property (
        @(posedge clk) disable iff (reset) (B == 1'b0) |=> (X == 1'b0)
    );

// When not in reset and both inputs are 1, X becomes 1 on the next cycle.
    check_one_when_both_one: assert property (
        @(posedge clk) disable iff (reset) (A == 1'b1 && B == 1'b1) |=> (X == 1'b1)
    );

endmodule
