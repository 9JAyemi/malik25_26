module sky130_fd_sc_ms__a211o_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // X matches the implemented OR-of-AND function.
    check_function_equivalence: assert property (
        @(posedge clk) X == ((A1 & A2) | B1 | C1)
    );

    // B1 high forces X high.
    check_b1_forces_x_high: assert property (
        @(posedge clk) B1 |-> X
    );

    // C1 high forces X high.
    check_c1_forces_x_high: assert property (
        @(posedge clk) C1 |-> X
    );

    // A1 and A2 high together force X high.
    check_a1_a2_force_x_high: assert property (
        @(posedge clk) (A1 & A2) |-> X
    );

    // With B1 and C1 low, X reduces to A1 OR A2.
    check_bc_low_reduces_to_a1_a2_or: assert property (
        @(posedge clk) (!B1 && !C1) |-> (X == (A1 | A2))
    );

    // With A1 and A2 low, X reduces to B1 OR C1.
    check_a1_a2_low_reduces_to_bc_or: assert property (
        @(posedge clk) (!A1 && !A2) |-> (X == (B1 | C1))
    );

    // X low requires B1 and C1 low and A1/A2 not both high.
    check_x_low_condition: assert property (
        @(posedge clk) (!X) |-> (!B1 && !C1 && !(A1 && A2))
    );

endmodule