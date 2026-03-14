module my_module_sva (
    input logic CLK,      // Sampling clock for assertions (DUT has no clock/reset)
    input logic X,        // DUT output
    input logic A,        // DUT input
    input logic SLEEP     // DUT input
);
    // X matches the RTL combinational expression.
    check_x_matches_rtl_expr: assert property (
        @(posedge CLK) X == (SLEEP ? (((A & SLEEP) & (~SLEEP)) | (A & SLEEP)) : A)
    );

    // X equals A for all cycles.
    check_x_equals_a: assert property (
        @(posedge CLK) X == A
    );

    // When SLEEP is 0, X equals A.
    check_sleep0_passthrough: assert property (
        @(posedge CLK) (SLEEP == 1'b0) |-> (X == A)
    );

    // When SLEEP is 1, X equals A.
    check_sleep1_passthrough: assert property (
        @(posedge CLK) (SLEEP == 1'b1) |-> (X == A)
    );

    // Rising SLEEP does not change X if A is stable.
    check_sleep_rise_no_effect_when_a_stable: assert property (
        @(posedge CLK) $rose(SLEEP) && $stable(A) |-> $stable(X)
    );

    // Falling SLEEP does not change X if A is stable.
    check_sleep_fall_no_effect_when_a_stable: assert property (
        @(posedge CLK) $fell(SLEEP) && $stable(A) |-> $stable(X)
    );

    // X rises when A rises.
    check_x_rises_with_a: assert property (
        @(posedge CLK) $rose(A) |-> $rose(X)
    );

    // X falls when A falls.
    check_x_falls_with_a: assert property (
        @(posedge CLK) $fell(A) |-> $fell(X)
    );

    // Any change on X implies a change on A.
    check_x_change_implies_a_change: assert property (
        @(posedge CLK) $changed(X) |-> $changed(A)
    );

    // The term (A & SLEEP) & (~SLEEP) is zero when SLEEP is 1.
    check_and_term_zero_on_sleep1: assert property (
        @(posedge CLK) (SLEEP == 1'b1) |-> (((A & SLEEP) & (~SLEEP)) == 1'b0)
    );
endmodule