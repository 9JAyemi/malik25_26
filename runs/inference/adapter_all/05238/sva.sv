module my_or2_8_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // X must match the implemented OR-with-invert behavior.
    check_x_matches_implemented_function: assert property (
        @($global_clock) X == (C ? ~((A | B)) : (A | B))
    );

    // When C is low, X must equal A OR B.
    check_c_low_selects_or: assert property (
        @($global_clock) !C |-> (X == (A | B))
    );

    // When C is high, X must equal the inverted OR of A and B.
    check_c_high_selects_inverted_or: assert property (
        @($global_clock) C |-> (X == ~(A | B))
    );

    // If both A and B are low, X must be low regardless of C.
    check_both_inputs_low_force_x_low: assert property (
        @($global_clock) (!A && !B) |-> (X == 1'b0)
    );

    // If both A and B are high, X must be high regardless of C.
    check_both_inputs_high_force_x_high: assert property (
        @($global_clock) (A && B) |-> (X == 1'b1)
    );

    // If A and B differ, X must match C.
    check_inputs_differ_follow_c: assert property (
        @($global_clock) (A ^ B) |-> (X == C)
    );

    // If A and B are equal, X must equal the inverse of that common value.
    check_inputs_equal_invert: assert property (
        @($global_clock) !(A ^ B) |-> (X == ~A)
    );

endmodule