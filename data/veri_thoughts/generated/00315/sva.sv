module sky130_fd_sc_ls__a21o_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic clk
);

    // X must implement (A1 & A2) | B1.
    check_function_equation: assert property (
        @(posedge clk) X == ((A1 & A2) | B1)
    );

    // B1 high must force X high through the OR stage.
    check_b1_forces_high: assert property (
        @(posedge clk) B1 |-> X
    );

    // A1 and A2 high must force X high through the AND stage.
    check_and_term_forces_high: assert property (
        @(posedge clk) (A1 && A2) |-> X
    );

    // With B1 low, X must reduce to the A1/A2 AND term.
    check_b1_low_reduces_to_and: assert property (
        @(posedge clk) !B1 |-> (X == (A1 & A2))
    );

    // With B1 low and the AND term false, X must be low.
    check_no_active_term_means_low: assert property (
        @(posedge clk) (!B1 && !(A1 && A2)) |-> !X
    );

    // A high X must come from B1 or from both A1 and A2.
    check_high_output_has_valid_cause: assert property (
        @(posedge clk) X |-> (B1 || (A1 && A2))
    );

endmodule