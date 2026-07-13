module sky130_fd_sc_hd__a211o_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // X matches the implemented AO211 function.
    check_function_equivalence: assert property (
        @(posedge clk) X == ((A1 & A2) | B1 | C1)
    );

    // B1 directly forces the OR output high.
    check_b1_forces_x_high: assert property (
        @(posedge clk) B1 |-> X
    );

    // C1 directly forces the OR output high.
    check_c1_forces_x_high: assert property (
        @(posedge clk) C1 |-> X
    );

    // A1 and A2 together force the AND path high.
    check_a1_a2_force_x_high: assert property (
        @(posedge clk) (A1 & A2) |-> X
    );

    // With B1 and C1 low, X reduces to the AND term.
    check_reduces_to_and_when_or_terms_low: assert property (
        @(posedge clk) (!B1 && !C1) |-> (X == (A1 & A2))
    );

    // A high X must come from one implemented source term.
    check_x_high_has_implemented_source: assert property (
        @(posedge clk) X |-> (B1 || C1 || (A1 && A2))
    );

endmodule