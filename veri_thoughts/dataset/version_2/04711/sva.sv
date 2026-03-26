module flip_flop_sva (
    input logic D,
    input logic CLK,
    input logic SET,
    input logic RESET,
    input logic Q,
    input logic Q_N
);

    // SET drives the outputs high/low when RESET is low.
    check_set_state: assert property (
        @(posedge CLK) disable iff (1'b0)
        (SET && !RESET) |=> (Q == 1'b1 && Q_N == 1'b0)
    );

    // SET has priority over RESET when both are high.
    check_set_priority_over_reset: assert property (
        @(posedge CLK) disable iff (1'b0)
        (SET && RESET) |=> (Q == 1'b1 && Q_N == 1'b0)
    );

    // RESET drives the outputs low/high when SET is low.
    check_reset_state: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!SET && RESET) |=> (Q == 1'b0 && Q_N == 1'b1)
    );

    // D=1 is captured when neither control input is asserted.
    check_data_capture_one: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!SET && !RESET && D) |=> (Q == 1'b1 && Q_N == 1'b0)
    );

    // D=0 is captured when neither control input is asserted.
    check_data_capture_zero: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!SET && !RESET && !D) |=> (Q == 1'b0 && Q_N == 1'b1)
    );

    // The outputs remain complementary after each clocked update.
    check_outputs_complementary: assert property (
        @(posedge CLK) disable iff (1'b0)
        1'b1 |=> (Q_N == ~Q)
    );

endmodule