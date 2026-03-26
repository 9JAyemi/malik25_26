module d_ff_async_rtl_sva (
    input logic D,
    input logic SET_B,
    input logic RESET_B,
    input logic CLK,
    input logic Q,
    input logic Q_N
);

    // CLK is the only clock; RESET_B and SET_B are synchronous active-high controls.

    // A sampled reset drives the outputs to the reset state on the next cycle.
    check_reset_state: assert property (
        @(posedge CLK) disable iff ($initstate)
        $past(RESET_B) |-> (Q === 1'b0 && Q_N === 1'b1)
    );

    // A sampled set drives the outputs to the set state when reset was low.
    check_set_state: assert property (
        @(posedge CLK) disable iff ($initstate)
        $past(!RESET_B && SET_B) |-> (Q === 1'b1 && Q_N === 1'b0)
    );

    // With reset and set low, the flop captures D and its inverse.
    check_data_capture: assert property (
        @(posedge CLK) disable iff ($initstate)
        $past(!RESET_B && !SET_B) |-> (Q === $past(D) && Q_N === ~$past(D))
    );

    // Reset has priority over set when both controls are high.
    check_reset_priority_over_set: assert property (
        @(posedge CLK) disable iff ($initstate)
        $past(RESET_B && SET_B) |-> (Q === 1'b0 && Q_N === 1'b1)
    );

    // The two outputs remain complementary after initialization.
    check_outputs_complementary: assert property (
        @(posedge CLK) disable iff ($initstate)
        1'b1 |-> (Q_N === ~Q)
    );

endmodule