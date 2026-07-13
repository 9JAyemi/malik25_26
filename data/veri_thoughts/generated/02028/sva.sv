module mux2_sva (
    input logic CLK,
    input logic X,
    input logic A0,
    input logic A1,
    input logic S
);
    // When S is 0, X equals A0.
    check_sel0_output_matches_A0: assert property (
        @(posedge CLK) disable iff ($initstate) (S === 1'b0) |-> (X === A0)
    );

    // When S is 1, X equals A1.
    check_sel1_output_matches_A1: assert property (
        @(posedge CLK) disable iff ($initstate) (S === 1'b1) |-> (X === A1)
    );

    // If A0 equals A1, X equals that value regardless of S.
    check_equal_inputs_drive_X: assert property (
        @(posedge CLK) disable iff ($initstate) (A0 === A1) |-> (X === A0)
    );

    // If inputs differ and X equals A0, S must be 0.
    check_consistency_X_eq_A0_implies_S0_when_inputs_differ: assert property (
        @(posedge CLK) disable iff ($initstate) ((A0 !== A1) && (X === A0)) |-> (S === 1'b0)
    );

    // If inputs differ and X equals A1, S must be 1.
    check_consistency_X_eq_A1_implies_S1_when_inputs_differ: assert property (
        @(posedge CLK) disable iff ($initstate) ((A0 !== A1) && (X === A1)) |-> (S === 1'b1)
    );

    // If S, A0, and A1 are stable, X is stable.
    check_stability_when_all_stable: assert property (
        @(posedge CLK) disable iff ($initstate) ($stable(S) && $stable(A0) && $stable(A1)) |-> $stable(X)
    );

    // On S rising edge with stable inputs, X now equals A1 and previously equaled A0.
    check_switch_to_A1_on_sel_rise_when_inputs_stable: assert property (
        @(posedge CLK) disable iff ($initstate) ($rose(S) && $stable(A0) && $stable(A1)) |-> ((X === A1) && ($past(X) === $past(A0)))
    );

    // On S falling edge with stable inputs, X now equals A0 and previously equaled A1.
    check_switch_to_A0_on_sel_fall_when_inputs_stable: assert property (
        @(posedge CLK) disable iff ($initstate) ($fell(S) && $stable(A0) && $stable(A1)) |-> ((X === A0) && ($past(X) === $past(A1)))
    );
endmodule