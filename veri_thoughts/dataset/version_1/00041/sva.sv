module karnaugh_map_assertions (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic F
);

    // F matches the implemented sum-of-products expression.
    check_f_matches_expression: assert property (
        @($global_clock)
        F == ((A & ~B & C & ~D) |
              (~A & B & ~C & D) |
              (A & ~B & ~C & D) |
              (~A & B & C & ~D))
    );

    // F is high for the minterm A=1, B=0, C=1, D=0.
    check_f_high_for_1010: assert property (
        @($global_clock)
        (A && !B && C && !D) |-> F
    );

    // F is high for the minterm A=0, B=1, C=0, D=1.
    check_f_high_for_0101: assert property (
        @($global_clock)
        (!A && B && !C && D) |-> F
    );

    // F is high for the minterm A=1, B=0, C=0, D=1.
    check_f_high_for_1001: assert property (
        @($global_clock)
        (A && !B && !C && D) |-> F
    );

    // F is high for the minterm A=0, B=1, C=1, D=0.
    check_f_high_for_0110: assert property (
        @($global_clock)
        (!A && B && C && !D) |-> F
    );

    // F is low when none of the implemented product terms is active.
    check_f_low_outside_implemented_minterms: assert property (
        @($global_clock)
        !((A & ~B & C & ~D) |
          (~A & B & ~C & D) |
          (A & ~B & ~C & D) |
          (~A & B & C & ~D)) |-> !F
    );

    // F can only be high when A and B differ.
    check_f_requires_ab_difference: assert property (
        @($global_clock)
        F |-> (A ^ B)
    );

    // F can only be high when C and D differ.
    check_f_requires_cd_difference: assert property (
        @($global_clock)
        F |-> (C ^ D)
    );

    // F is low whenever A and B are equal.
    check_f_low_when_ab_equal: assert property (
        @($global_clock)
        !(A ^ B) |-> !F
    );

    // F is low whenever C and D are equal.
    check_f_low_when_cd_equal: assert property (
        @($global_clock)
        !(C ^ D) |-> !F
    );

endmodule