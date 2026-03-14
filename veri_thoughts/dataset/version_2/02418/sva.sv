module mux_2to1_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic S,
    input logic Y
);
    // Y implements 2:1 mux function: Y = (~S & A) | (S & B).
    check_mux_function: assert property (
        @(posedge CLK) Y == ((~S & A) | (S & B))
    );

    // When S=0, Y equals A.
    check_select_low: assert property (
        @(posedge CLK) (S == 1'b0) |-> (Y == A)
    );

    // When S=1, Y equals B.
    check_select_high: assert property (
        @(posedge CLK) (S == 1'b1) |-> (Y == B)
    );

    // If A and B are equal, Y equals that value.
    check_equal_inputs: assert property (
        @(posedge CLK) (A == B) |-> (Y == A)
    );

    // If A, B, and S do not change between cycles, Y does not change.
    check_output_stable_if_inputs_stable: assert property (
        @(posedge CLK) (!$changed(A) && !$changed(B) && !$changed(S)) |-> (!$changed(Y))
    );

    // With S held low across cycles, Y change matches A change.
    check_track_A_when_S_low_stable: assert property (
        @(posedge CLK) ($past(1'b1) && (S == 1'b0) && ($past(S) == 1'b0)) |-> ($changed(Y) == $changed(A))
    );

    // With S held high across cycles, Y change matches B change.
    check_track_B_when_S_high_stable: assert property (
        @(posedge CLK) ($past(1'b1) && (S == 1'b1) && ($past(S) == 1'b1)) |-> ($changed(Y) == $changed(B))
    );

    // On S rising edge, Y equals B in the same cycle.
    check_on_S_rise: assert property (
        @(posedge CLK) $rose(S) |-> (Y == B)
    );

    // On S falling edge, Y equals A in the same cycle.
    check_on_S_fall: assert property (
        @(posedge CLK) $fell(S) |-> (Y == A)
    );

    // With S low across cycles and A stable, Y is stable regardless of B.
    check_B_irrelevant_when_S_low: assert property (
        @(posedge CLK) ($past(1'b1) && (S == 1'b0) && ($past(S) == 1'b0) && !$changed(A)) |-> (!$changed(Y))
    );

    // With S high across cycles and B stable, Y is stable regardless of A.
    check_A_irrelevant_when_S_high: assert property (
        @(posedge CLK) ($past(1'b1) && (S == 1'b1) && ($past(S) == 1'b1) && !$changed(B)) |-> (!$changed(Y))
    );
endmodule