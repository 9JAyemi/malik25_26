module sky130_fd_sc_hdll__a211oi_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // Full combinational AOI211 function sampled on $global_clock.
    check_functional_equivalence: assert property (
        @($global_clock) Y === ~((A1 & A2) | B1 | C1)
    );

    // B1 high forces the output low.
    check_b1_forces_low: assert property (
        @($global_clock) B1 |-> !Y
    );

    // C1 high forces the output low.
    check_c1_forces_low: assert property (
        @($global_clock) C1 |-> !Y
    );

    // A1 and A2 high together force the output low.
    check_a1_a2_forces_low: assert property (
        @($global_clock) (A1 && A2) |-> !Y
    );

    // If no NOR input term is active, the output is high.
    check_no_active_term_gives_high: assert property (
        @($global_clock) (!B1 && !C1 && !(A1 && A2)) |-> Y
    );

    // With B1 and C1 low, Y reduces to the inversion of A1&A2.
    check_reduced_a_term_when_b1_c1_low: assert property (
        @($global_clock) (!B1 && !C1) |-> (Y === ~(A1 & A2))
    );

endmodule