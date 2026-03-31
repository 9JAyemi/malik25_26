module and_gate_sva (
    input logic A,
    input logic B,
    input logic clk,
    input logic reset,
    input logic X
);

    // X is low after a cycle with reset asserted.
    check_reset_clears_x: assert property (
        @(posedge clk) reset |=> (X == 1'b0)
    );

    // X is low after a cycle where A and B are not both high.
    check_and_low_when_inputs_low: assert property (
        @(posedge clk) disable iff (reset)
        ((A == 1'b0) || (B == 1'b0)) |=> (X == 1'b0)
    );

    // X is high after a cycle where A and B are both high.
    check_and_high_when_inputs_high: assert property (
        @(posedge clk) disable iff (reset)
        ((A == 1'b1) && (B == 1'b1)) |=> (X == 1'b1)
    );

endmodule