module and3_sva(
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic X
);

    // X must equal the AND of A, B, and C.
    check_x_matches_and3: assert property (
        @(posedge clk) X == (A & B & C)
    );

    // X high requires all three inputs to be high.
    check_x_high_implies_all_inputs_high: assert property (
        @(posedge clk) X |-> (A && B && C)
    );

    // All three inputs high must drive X high.
    check_all_inputs_high_implies_x_high: assert property (
        @(posedge clk) (A && B && C) |-> X
    );

    // Any low input must force X low.
    check_any_low_input_forces_x_low: assert property (
        @(posedge clk) ((!A) || (!B) || (!C)) |-> !X
    );

endmodule