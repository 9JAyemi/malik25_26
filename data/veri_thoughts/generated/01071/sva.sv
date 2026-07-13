module sky130_fd_sc_ms__a211o_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);
    // Combinational gate; assertions clocked on $global_clock.

    // X equals (A1 & A2) OR B1 OR C1.
    check_x_eq_logic: assert property (
        @(posedge $global_clock) X == ((A1 & A2) | B1 | C1)
    );

    // B1 high forces X high.
    check_b1_forces_x: assert property (
        @(posedge $global_clock) (B1 == 1'b1) |-> (X == 1'b1)
    );

    // C1 high forces X high.
    check_c1_forces_x: assert property (
        @(posedge $global_clock) (C1 == 1'b1) |-> (X == 1'b1)
    );

    // A1 & A2 high forces X high.
    check_a1a2_forces_x: assert property (
        @(posedge $global_clock) ((A1 & A2) == 1'b1) |-> (X == 1'b1)
    );

    // All inputs low force X low.
    check_all_zero_forces_x0: assert property (
        @(posedge $global_clock) ((A1 == 1'b0) && (A2 == 1'b0) && (B1 == 1'b0) && (C1 == 1'b0)) |-> (X == 1'b0)
    );

    // X low implies B1=0, C1=0, and not (A1 & A2).
    check_x0_implies_inputs_zeroish: assert property (
        @(posedge $global_clock) (X == 1'b0) |-> ((B1 == 1'b0) && (C1 == 1'b0) && ((A1 & A2) == 1'b0))
    );

    // With B1=0 and C1=0, X equals A1 & A2.
    check_reduce_to_and_when_b1c1_zero: assert property (
        @(posedge $global_clock) ((B1 == 1'b0) && (C1 == 1'b0)) |-> (X == (A1 & A2))
    );

    // If X=1 and B1=C1=0, then A1 & A2 must be 1.
    check_x1_no_b1c1_requires_and: assert property (
        @(posedge $global_clock) ((X == 1'b1) && (B1 == 1'b0) && (C1 == 1'b0)) |-> ((A1 & A2) == 1'b1)
    );

    // X=1 implies B1=1 or C1=1 or A1 & A2=1.
    check_x1_implies_some_term_true: assert property (
        @(posedge $global_clock) (X == 1'b1) |-> ((B1 == 1'b1) || (C1 == 1'b1) || ((A1 & A2) == 1'b1))
    );

    // If B1=0, C1=0, and A1 & A2=0 then X must be 0.
    check_b1c1zero_andzero_implies_x0: assert property (
        @(posedge $global_clock) ((B1 == 1'b0) && (C1 == 1'b0) && ((A1 & A2) == 1'b0)) |-> (X == 1'b0)
    );

endmodule