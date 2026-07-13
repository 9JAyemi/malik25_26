module mux_2to1_enable_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic EN,
    input logic Y
);

    // Y implements a 2:1 mux with EN selecting A over B.
    check_mux_function: assert property (
        @(posedge CLK) Y == (EN ? A : B)
    );

    // When EN is 1, Y equals A.
    check_select_a_when_en: assert property (
        @(posedge CLK) EN |-> (Y == A)
    );

    // When EN is 0, Y equals B.
    check_select_b_when_not_en: assert property (
        @(posedge CLK) !EN |-> (Y == B)
    );

    // On EN rising edge, Y equals A in the same cycle.
    check_en_rise_selects_a: assert property (
        @(posedge CLK) $rose(EN) |-> (Y == A)
    );

    // On EN falling edge, Y equals B in the same cycle.
    check_en_fall_selects_b: assert property (
        @(posedge CLK) $fell(EN) |-> (Y == B)
    );

    // Y can change only if EN or one of the inputs changes.
    check_y_changes_only_on_input_change: assert property (
        @(posedge CLK) $changed(Y) |-> ($changed(EN) || $changed(A) || $changed(B))
    );

    // With EN held high across cycles, Y change matches A change.
    check_y_follows_a_when_en_held_high: assert property (
        @(posedge CLK) (EN && $past(EN)) |-> ($changed(Y) == $changed(A))
    );

    // With EN held low across cycles, Y change matches B change.
    check_y_follows_b_when_en_held_low: assert property (
        @(posedge CLK) (!EN && !$past(EN)) |-> ($changed(Y) == $changed(B))
    );

endmodule