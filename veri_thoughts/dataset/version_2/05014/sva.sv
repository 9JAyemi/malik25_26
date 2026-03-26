module Adder_sva (
    input logic clk,
    input logic rst,
    input logic load,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] Q
);

    // Reset clears Q on the following clock sample.
    check_reset_clears_q: assert property (
        @(posedge clk) rst |=> (Q == 4'h0)
    );

    // A load captures the current 4-bit sum of A and B.
    check_load_captures_sum: assert property (
        @(posedge clk) disable iff (rst) load |=> (Q == $past(A + B))
    );

    // Without a load, Q holds its previous value.
    check_hold_when_not_load: assert property (
        @(posedge clk) disable iff (rst) !load |=> (Q == $past(Q))
    );

    // Reset overrides load when both are asserted together.
    check_reset_priority_over_load: assert property (
        @(posedge clk) rst && load |=> (Q == 4'h0)
    );

endmodule