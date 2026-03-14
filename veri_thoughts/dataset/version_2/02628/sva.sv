module d_ff_en_0_sva (
    input  logic [0:0] d_ff3_sign_out,
    input  logic [1:0] FSM_sequential_state_reg,
    input  logic [0:0] Q,
    input  logic       CLK,
    input  logic       EN
);
    // Clock: CLK (posedge). Reset: EN active-low, asynchronous.

    ///// Asynchronous reset behavior /////
    // When EN is LOW at a clock edge, output must be 0.
    reset_level_forces_zero: assert property (
        @(posedge CLK) (EN == 1'b0) |-> (d_ff3_sign_out == 1'b0)
    );

    // On a falling edge of EN between clocks, output must be 0 at the next clock.
    reset_fall_clears_output: assert property (
        @(posedge CLK) $fell(EN) |-> (d_ff3_sign_out == 1'b0)
    );

    // While EN stays LOW across cycles, output remains 0 and stable.
    reset_hold_zero_and_stable: assert property (
        @(posedge CLK) (!EN && !$past(EN)) |-> (d_ff3_sign_out == 1'b0 && $stable(d_ff3_sign_out))
    );

    ///// Enabled capture behavior /////
    // With EN HIGH for two consecutive cycles, output equals previous cycle's Q.
    capture_when_enabled_two_cycles: assert property (
        @(posedge CLK) disable iff (!EN) ($past(EN) && EN) |-> (d_ff3_sign_out == $past(Q))
    );

    // With EN HIGH for two consecutive cycles and Q unchanged, output remains unchanged.
    hold_when_input_stable_and_enabled: assert property (
        @(posedge CLK) disable iff (!EN) ($past(EN) && EN && (Q == $past(Q))) |-> (d_ff3_sign_out == $past(d_ff3_sign_out))
    );

    // With EN HIGH for two consecutive cycles and Q changed last cycle, output changes accordingly.
    reflect_input_change_when_enabled: assert property (
        @(posedge CLK) disable iff (!EN) ($past(EN) && EN && (Q != $past(Q))) |-> (d_ff3_sign_out != $past(d_ff3_sign_out))
    );
endmodule