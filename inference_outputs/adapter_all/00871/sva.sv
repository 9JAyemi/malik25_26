module and_gate_sva (
    input logic A,
    input logic B,
    input logic clk,
    input logic reset,
    input logic X
);

    // X is cleared on the cycle after reset is asserted.
    check_reset_clears_x: assert property (
        @(posedge clk) reset |=> (X == 1'b0)
    );

    // X reflects the AND of A and B from the previous cycle.
    check_and_update: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (X == ($past(A) & $past(B)))
    );

    // A high X requires both previous inputs to have been high.
    check_x_high_requires_prev_inputs_high: assert property (
        @(posedge clk) disable iff (reset)
        (X == 1'b1) |-> (($past(A) == 1'b1) && ($past(B) == 1'b1))
    );

    // Both previous inputs high must produce a high X.
    check_prev_inputs_high_produce_x_high: assert property (
        @(posedge clk) disable iff (reset)
        (($past(A) == 1'b1) && ($past(B) == 1'b1)) |-> (X == 1'b1)
    );

    // A low X means at least one previous input was low.
    check_x_low_requires_prev_input_low: assert property (
        @(posedge clk) disable iff (reset)
        (X == 1'b0) |-> (($past(A) == 1'b0) || ($past(B) == 1'b0))
    );

endmodule