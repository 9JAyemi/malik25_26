module logic_gate_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1,
    input logic X
);

    // X matches the RTL assign expression exactly.
    check_x_matches_rtl_expression: assert property (
        @($global_clock)
        X == ((((A1 == 1'b1) && (A2 == 1'b0)) || ((B1 == 1'b1) && (C1 == 1'b0))) ? 1'b1 :
              ((D1 == 1'b1) ? 1'b0 : 1'b0))
    );

    // condition1 drives X high.
    check_condition1_forces_x_high: assert property (
        @($global_clock)
        ((A1 == 1'b1) && (A2 == 1'b0)) |-> (X == 1'b1)
    );

    // condition2 drives X high.
    check_condition2_forces_x_high: assert property (
        @($global_clock)
        ((B1 == 1'b1) && (C1 == 1'b0)) |-> (X == 1'b1)
    );

    // D1 alone drives the low branch when the other conditions are false.
    check_d1_branch_keeps_x_low: assert property (
        @($global_clock)
        (!(((A1 == 1'b1) && (A2 == 1'b0)) || ((B1 == 1'b1) && (C1 == 1'b0))) && (D1 == 1'b1))
        |-> (X == 1'b0)
    );

    // The default branch keeps X low when all conditions are false.
    check_default_branch_keeps_x_low: assert property (
        @($global_clock)
        (!(((A1 == 1'b1) && (A2 == 1'b0)) || ((B1 == 1'b1) && (C1 == 1'b0))) && (D1 == 1'b0))
        |-> (X == 1'b0)
    );

    // X can only be high when condition1 or condition2 is true.
    check_x_high_requires_primary_condition: assert property (
        @($global_clock)
        (X == 1'b1) |-> (((A1 == 1'b1) && (A2 == 1'b0)) || ((B1 == 1'b1) && (C1 == 1'b0)))
    );

    // The high branch has priority over D1 when both are true.
    check_primary_condition_overrides_d1: assert property (
        @($global_clock)
        ((((A1 == 1'b1) && (A2 == 1'b0)) || ((B1 == 1'b1) && (C1 == 1'b0))) && (D1 == 1'b1))
        |-> (X == 1'b1)
    );

endmodule