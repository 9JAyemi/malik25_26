module sky130_fd_sc_hd__a211oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // Y matches the implemented NOR of the AND term and the two B/C inputs.
    check_functional_equivalence: assert property (
        @(posedge clk) Y == ~((A1 & A2) | B1 | C1)
    );

    // B1 high forces the NOR output low.
    check_b1_forces_low: assert property (
        @(posedge clk) B1 |-> !Y
    );

    // C1 high forces the NOR output low.
    check_c1_forces_low: assert property (
        @(posedge clk) C1 |-> !Y
    );

    // Both A inputs high force the AND term high and drive Y low.
    check_and_term_forces_low: assert property (
        @(posedge clk) (A1 & A2) |-> !Y
    );

    // With B1 and C1 low, Y reduces to the inverted AND of A1 and A2.
    check_bc_low_reduces_to_and: assert property (
        @(posedge clk) (!B1 && !C1) |-> (Y == ~(A1 & A2))
    );

    // With the AND term low, Y reduces to the inverted OR of B1 and C1.
    check_and_low_reduces_to_or: assert property (
        @(posedge clk) !(A1 & A2) |-> (Y == ~(B1 | C1))
    );

    // If B1 and C1 are low and the AND term is high, Y must be low.
    check_all_active_inputs_drive_low: assert property (
        @(posedge clk) (!B1 && !C1 && (A1 & A2)) |-> !Y
    );

    // If B1 and C1 are low and the AND term is low, Y must be high.
    check_all_inactive_inputs_drive_high: assert property (
        @(posedge clk) (!B1 && !C1 && !(A1 & A2)) |-> Y
    );

endmodule