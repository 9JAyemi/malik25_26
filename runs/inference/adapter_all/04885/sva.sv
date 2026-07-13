module sky130_fd_sc_ls__o211a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // X matches the implemented OR-then-AND function.
    check_functional_equivalence: assert property (
        @(posedge clk) X == ((A1 | A2) & B1 & C1)
    );

    // B1 low forces the AND stage low and X low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) !B1 |-> !X
    );

    // C1 low forces the AND stage low and X low.
    check_c1_low_forces_x_low: assert property (
        @(posedge clk) !C1 |-> !X
    );

    // Both A inputs low force the OR stage low and X low.
    check_a_inputs_low_force_x_low: assert property (
        @(posedge clk) (!A1 && !A2) |-> !X
    );

    // X high requires B1, C1, and at least one A input high.
    check_x_high_requires_all_enables: assert property (
        @(posedge clk) X |-> (B1 && C1 && (A1 || A2))
    );

    // With B1 and C1 high, X reduces to the OR of the A inputs.
    check_b1_c1_high_reduces_to_or: assert property (
        @(posedge clk) (B1 && C1) |-> (X == (A1 | A2))
    );

    // With B1 and C1 high, X high requires at least one A input high.
    check_b1_c1_high_x_high_requires_a_or: assert property (
        @(posedge clk) (B1 && C1 && X) |-> (A1 || A2)
    );

    // With B1 and C1 high, both A inputs high force X high.
    check_b1_c1_high_a_or_forces_x_high: assert property (
        @(posedge clk) (B1 && C1 && (A1 || A2)) |-> X
    );

endmodule