module d_latch_assertions (
    input logic CLK,
    input logic D,
    input logic RESET,
    input logic EN,
    input logic Q,
    input logic Q_N
);

    // Previous-cycle reset drives the reset output state.
    check_reset_state: assert property (
        @(posedge CLK) disable iff ($initstate)
        $past(RESET) |-> (Q == 1'b0 && Q_N == 1'b1)
    );

    // Previous-cycle enabled update captures D and its complement.
    check_capture_when_enabled: assert property (
        @(posedge CLK) disable iff (RESET || $initstate)
        (!$past(RESET) && $past(EN)) |-> (Q == $past(D) && Q_N == ~$past(D))
    );

    // Previous-cycle disabled update holds both outputs.
    check_hold_when_disabled: assert property (
        @(posedge CLK) disable iff (RESET || $initstate)
        (!$past(RESET) && !$past(EN)) |-> (Q == $past(Q) && Q_N == $past(Q_N))
    );

    // Reset or enabled capture produces complementary outputs.
    check_complement_after_update: assert property (
        @(posedge CLK) disable iff ($initstate)
        ($past(RESET) || (!$past(RESET) && $past(EN))) |-> (Q_N == ~Q)
    );

    // A valid complementary state stays complementary while disabled.
    check_complement_preserved_on_hold: assert property (
        @(posedge CLK) disable iff (RESET || $initstate)
        (!$past(RESET) && !$past(EN) && ($past(Q_N) == ~$past(Q))) |-> (Q_N == ~Q)
    );

endmodule