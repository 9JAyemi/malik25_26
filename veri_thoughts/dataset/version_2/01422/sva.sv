module nand_mux_sva (
    input logic CLK,  // assertion clock for sampling (RTL is combinational)
    input logic A,
    input logic B,
    input logic SEL,
    input logic Y
);
    // Analysis: No clock or reset in RTL; pure combinational mux. Y = (SEL ? B : A).

    // Y equals 2:1 mux function of A and B selected by SEL.
    check_mux_function: assert property (
        @(posedge CLK) Y == ((SEL & B) | ((~SEL) & A))
    );

    // When SEL is LOW, Y equals A.
    check_select_A_when_sel_low: assert property (
        @(posedge CLK) !SEL |-> (Y == A)
    );

    // When SEL is HIGH, Y equals B.
    check_select_B_when_sel_high: assert property (
        @(posedge CLK) SEL |-> (Y == B)
    );

    // Y always equals either A or B.
    check_output_is_A_or_B: assert property (
        @(posedge CLK) (Y == A) || (Y == B)
    );

    // If inputs A,B,SEL are stable, Y remains stable.
    check_stable_inputs_hold_output: assert property (
        @(posedge CLK) $stable({A,B,SEL}) |-> $stable(Y)
    );

    // Y changes only if at least one of A,B,SEL changes.
    check_output_change_has_cause: assert property (
        @(posedge CLK) $changed(Y) |-> $changed({A,B,SEL})
    );

    // If only SEL toggles and A!=B, Y must toggle.
    check_sel_toggle_changes_output_when_inputs_differ: assert property (
        @(posedge CLK) ($changed(SEL) && $stable(A) && $stable(B) && (A != B)) |-> $changed(Y)
    );

    // If only SEL toggles and A==B, Y must not change.
    check_sel_toggle_no_effect_when_inputs_equal: assert property (
        @(posedge CLK) ($changed(SEL) && $stable(A) && $stable(B) && (A == B)) |-> $stable(Y)
    );

    // With SEL LOW and A stable, Y remains stable regardless of B.
    check_sel0_A_stable_keeps_Y_stable: assert property (
        @(posedge CLK) (!SEL && $stable(SEL) && $stable(A)) |-> $stable(Y)
    );

    // With SEL HIGH and B stable, Y remains stable regardless of A.
    check_sel1_B_stable_keeps_Y_stable: assert property (
        @(posedge CLK) (SEL && $stable(SEL) && $stable(B)) |-> $stable(Y)
    );

    // With SEL LOW and A changes, Y must change accordingly.
    check_sel0_A_change_causes_Y_change: assert property (
        @(posedge CLK) (!SEL && $stable(SEL) && $changed(A)) |-> $changed(Y)
    );

    // With SEL HIGH and B changes, Y must change accordingly.
    check_sel1_B_change_causes_Y_change: assert property (
        @(posedge CLK) (SEL && $stable(SEL) && $changed(B)) |-> $changed(Y)
    );

    // If A equals B, Y equals that common value.
    check_equal_inputs_result: assert property (
        @(posedge CLK) (A == B) |-> (Y == A)
    );
endmodule