module flip_flop_sva (
    input logic D,
    input logic SET,
    input logic SLEEP_B,
    input logic KAPWR,
    input logic VGND,
    input logic VPWR,
    input logic Q,
    input logic CLK
);

    // Next-state function: Q_next = (SET ? 1 : (SLEEP_B ? 0 : D)).
    check_next_state_function: assert property (
        @(posedge CLK) 1'b1 |=> (Q == (SET ? 1'b1 : (SLEEP_B ? 1'b0 : D)))
    );

    // SET forces Q to 1 on the next clock.
    check_set_forces_one: assert property (
        @(posedge CLK) SET |=> (Q == 1'b1)
    );

    // When both SET and SLEEP_B are high, SET has priority and Q becomes 1.
    check_set_overrides_sleep: assert property (
        @(posedge CLK) (SET && SLEEP_B) |=> (Q == 1'b1)
    );

    // With SET low and SLEEP_B high, Q is cleared to 0.
    check_sleep_clears_when_no_set: assert property (
        @(posedge CLK) (!SET && SLEEP_B) |=> (Q == 1'b0)
    );

    // With both SET and SLEEP_B low, Q captures D.
    check_passthrough_d_when_no_controls: assert property (
        @(posedge CLK) (!SET && !SLEEP_B) |=> (Q == D)
    );

    // With no controls and D=1, Q becomes 1 next cycle.
    check_d1_captured_when_no_controls: assert property (
        @(posedge CLK) (!SET && !SLEEP_B && (D == 1'b1)) |=> (Q == 1'b1)
    );

    // With no controls and D=0, Q becomes 0 next cycle.
    check_d0_captured_when_no_controls: assert property (
        @(posedge CLK) (!SET && !SLEEP_B && (D == 1'b0)) |=> (Q == 1'b0)
    );

endmodule