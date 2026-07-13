module my_module_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // X must equal the OR of the three-input AND term and B1.
    check_x_matches_or_function: assert property (
        @($global_clock) X == ((A1 & A2 & A3) | B1)
    );

    // B1 high must force X high.
    check_b1_forces_x_high: assert property (
        @($global_clock) B1 |-> X
    );

    // All three A inputs high must force X high.
    check_a_term_forces_x_high: assert property (
        @($global_clock) (A1 & A2 & A3) |-> X
    );

    // With B1 low, X must equal the three-input AND term.
    check_b1_low_reduces_to_and_term: assert property (
        @($global_clock) !B1 |-> (X == (A1 & A2 & A3))
    );

    // With the AND term low, X must equal B1.
    check_and_term_low_reduces_to_b1: assert property (
        @($global_clock) !(A1 & A2 & A3) |-> (X == B1)
    );

    // X low requires B1 low and the three-input AND term low.
    check_x_low_requires_both_terms_low: assert property (
        @($global_clock) !X |-> (!B1 && !(A1 & A2 & A3))
    );

    // X high requires B1 high or the three-input AND term high.
    check_x_high_requires_some_term_high: assert property (
        @($global_clock) X |-> (B1 || (A1 & A2 & A3))
    );

endmodule