module DFFSR_sva (
    input logic CLK,
    input logic D,
    input logic SET,
    input logic RESET,
    input logic Q,
    input logic QN
);

    // QN is always the inverse of Q.
    check_qn_is_inverse_of_q: assert property (
        @(posedge CLK) disable iff (1'b0) (QN === ~Q)
    );

    // SET alone drives Q high on the next cycle.
    check_set_drives_q_high: assert property (
        @(posedge CLK) disable iff (1'b0) (SET && !RESET) |=> (Q === 1'b1)
    );

    // SET has priority over RESET on the next cycle.
    check_set_overrides_reset: assert property (
        @(posedge CLK) disable iff (1'b0) (SET && RESET) |=> (Q === 1'b1)
    );

    // RESET drives Q low when SET is low.
    check_reset_drives_q_low: assert property (
        @(posedge CLK) disable iff (1'b0) (!SET && RESET) |=> (Q === 1'b0)
    );

    // D is captured when SET and RESET are low.
    check_data_capture: assert property (
        @(posedge CLK) disable iff (1'b0) (!SET && !RESET) |=> (Q === $past(D))
    );

endmodule