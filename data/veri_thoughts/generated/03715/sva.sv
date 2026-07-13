module top_module_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C,
    input logic       SEL1,
    input logic       SEL2,
    input logic [3:0] OUT
);

    // OUT matches the implemented top-level function.
    check_output_function: assert property (
        @($global_clock) OUT == (SEL2 ? (SEL1 ? C : 4'b0000) : 4'b0000)
    );

    // Any low select forces OUT to zero.
    check_any_low_select_forces_zero: assert property (
        @($global_clock) (!SEL1 || !SEL2) |-> (OUT == 4'b0000)
    );

    // Both selects high pass C through to OUT.
    check_both_selects_pass_c: assert property (
        @($global_clock) (SEL1 && SEL2) |-> (OUT == C)
    );

    // A does not affect OUT when other controlling inputs are unchanged.
    check_a_independent_of_out: assert property (
        @($global_clock)
        ($changed(A) && $stable(B) && $stable(C) && $stable(SEL1) && $stable(SEL2))
        |-> $stable(OUT)
    );

    // B does not affect OUT when other controlling inputs are unchanged.
    check_b_independent_of_out: assert property (
        @($global_clock)
        ($changed(B) && $stable(A) && $stable(C) && $stable(SEL1) && $stable(SEL2))
        |-> $stable(OUT)
    );

    // C is blocked from OUT when either select is low.
    check_c_blocked_when_select_disabled: assert property (
        @($global_clock)
        ($changed(C) && $stable(A) && $stable(B) && $stable(SEL1) && $stable(SEL2) && (!SEL1 || !SEL2))
        |-> $stable(OUT)
    );

    // C propagates to OUT when both selects are high.
    check_c_propagates_when_enabled: assert property (
        @($global_clock)
        ($changed(C) && $stable(A) && $stable(B) && $stable(SEL1) && $stable(SEL2) && SEL1 && SEL2)
        |-> ($changed(OUT) && (OUT == C))
    );

endmodule