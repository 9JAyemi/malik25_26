module flip_flop_async_reset_set_sva (
    input logic D,
    input logic RESET_B,
    input logic SET_B,
    input logic CLK,
    input logic Q,
    input logic Q_B
);

    // Low RESET_B forces the reset state on the next cycle.
    check_reset_value: assert property (
        @(posedge CLK)
        !RESET_B |=> (Q == 1'b0 && Q_B == 1'b1)
    );

    // Low RESET_B overrides low SET_B.
    check_reset_priority_over_set: assert property (
        @(posedge CLK)
        (!RESET_B && !SET_B) |=> (Q == 1'b0 && Q_B == 1'b1)
    );

    // Low SET_B forces the set state when reset is inactive.
    check_set_value: assert property (
        @(posedge CLK) disable iff (!RESET_B)
        !SET_B |=> (Q == 1'b1 && Q_B == 1'b0)
    );

    // With reset and set inactive, D=1 is captured on the next cycle.
    check_capture_d_high: assert property (
        @(posedge CLK) disable iff (!RESET_B)
        (SET_B && D) |=> (Q == 1'b1 && Q_B == 1'b0)
    );

    // With reset and set inactive, D=0 is captured on the next cycle.
    check_capture_d_low: assert property (
        @(posedge CLK) disable iff (!RESET_B)
        (SET_B && !D) |=> (Q == 1'b0 && Q_B == 1'b1)
    );

    // The two outputs remain complementary after each clocked update.
    check_outputs_complementary: assert property (
        @(posedge CLK)
        1'b1 |=> (Q_B == ~Q)
    );

endmodule