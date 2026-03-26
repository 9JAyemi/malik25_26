module dff_with_async_set_reset_assertions (
    input logic D,
    input logic SET,
    input logic RESET,
    input logic CLK,
    input logic Q
);

    // CLK is the only clock; SET and RESET are synchronous active-high controls.
    // There is no separate assertion reset in this RTL.

    // Q starts low because Q_reg is initialized to 0.
    check_init_low: assert property (
        @(posedge CLK) disable iff (1'b0) $initstate |-> (Q == 1'b0)
    );

    // SET has highest priority and drives Q high on the next sampled cycle.
    check_set_forces_one: assert property (
        @(posedge CLK) disable iff (1'b0) SET |=> (Q == 1'b1)
    );

    // RESET drives Q low on the next sampled cycle when SET is low.
    check_reset_forces_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (!SET && RESET) |=> (Q == 1'b0)
    );

    // With both controls low, Q captures D on the next sampled cycle.
    check_data_capture: assert property (
        @(posedge CLK) disable iff (1'b0) (!SET && !RESET) |=> (Q == $past(D))
    );

    // When both controls are high, SET takes priority over RESET.
    check_set_priority_over_reset: assert property (
        @(posedge CLK) disable iff (1'b0) (SET && RESET) |=> (Q == 1'b1)
    );

    // A rising Q must come from SET or from capturing a 1 on D.
    check_rise_has_valid_cause: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!$initstate && $rose(Q)) |-> ($past(SET) || (!$past(SET) && !$past(RESET) && $past(D)))
    );

    // A falling Q must come from RESET or from capturing a 0 on D.
    check_fall_has_valid_cause: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!$initstate && $fell(Q)) |-> (!$past(SET) && ($past(RESET) || (!$past(RESET) && !$past(D))))
    );

endmodule