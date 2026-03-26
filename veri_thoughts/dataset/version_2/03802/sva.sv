module my_logic_gate_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // No RTL clock or reset; sample the combinational behavior on $global_clock.

    // Output matches the implemented combinational equation.
    check_output_matches_rtl: assert property (
        @($global_clock)
        X == (((A1 & A2 & ~B1 & ~C1) | (A1 | A2 | (B1 & C1)) | (~A1 & A2 & B1 & C1)) ? 1'b1 : 1'b0)
    );

    // A1 high forces the output high.
    check_a1_forces_high: assert property (
        @($global_clock)
        A1 |-> (X == 1'b1)
    );

    // A2 high forces the output high.
    check_a2_forces_high: assert property (
        @($global_clock)
        A2 |-> (X == 1'b1)
    );

    // B1 and C1 high together force the output high.
    check_b1_c1_force_high: assert property (
        @($global_clock)
        (B1 && C1) |-> (X == 1'b1)
    );

    // Without A1 or A2, the output stays low unless both B1 and C1 are high.
    check_low_when_no_enabling_term: assert property (
        @($global_clock)
        (!A1 && !A2 && (!B1 || !C1)) |-> (X == 1'b0)
    );

endmodule

bind my_logic_gate my_logic_gate_sva my_logic_gate_sva_inst (
    .X(X),
    .A1(A1),
    .A2(A2),
    .B1(B1),
    .C1(C1)
);