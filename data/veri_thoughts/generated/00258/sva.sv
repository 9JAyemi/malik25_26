module logic_expression_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic E,
    input logic X
);

    // X matches the full RTL sum-of-products expression.
    check_x_matches_full_expression: assert property (
        @($global_clock)
        X == ((~A & ~B & ~C & D & ~E) |
              (~A & ~B & ~C & D & E)  |
              (~A & ~B & C & ~D & E)  |
              (~A & ~B & C & D & E)   |
              (~A & B & ~C & ~D & E)  |
              (~A & B & ~C & D & E)   |
              (~A & B & C & ~D & E)   |
              (A & ~B & ~C & ~D & E)  |
              (A & ~B & ~C & D & E)   |
              (A & ~B & C & D & E)    |
              (A & B & C & ~D & E)    |
              (A & B & C & D & E))
    );

    // When E is low, only the w1 term can make X high.
    check_e_low_behavior: assert property (
        @($global_clock)
        (~E) |-> (X == (~A & ~B & ~C & D))
    );

    // For A=0, B=0, E=1, X reduces to C or D.
    check_ab00_e_high_behavior: assert property (
        @($global_clock)
        (~A & ~B & E) |-> (X == (C | D))
    );

    // For A=0, B=1, E=1, X reduces to not C or not D.
    check_ab01_e_high_behavior: assert property (
        @($global_clock)
        (~A & B & E) |-> (X == (~C | ~D))
    );

    // For A=1, B=0, E=1, X reduces to not C or D.
    check_ab10_e_high_behavior: assert property (
        @($global_clock)
        (A & ~B & E) |-> (X == (~C | D))
    );

    // For A=1, B=1, E=1, X reduces to C.
    check_ab11_e_high_behavior: assert property (
        @($global_clock)
        (A & B & E) |-> (X == C)
    );

endmodule