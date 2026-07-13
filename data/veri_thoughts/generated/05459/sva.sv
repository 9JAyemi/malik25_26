module dff_asr_sva (
    input logic D,
    input logic CLK,
    input logic SET_B,
    input logic RESET_B,
    input logic Q,
    input logic Q_N
);

    // Q_N is the complement of Q when reset is inactive.
    check_qn_inverse: assert property (
        @(posedge CLK) disable iff (!RESET_B) (Q_N == ~Q)
    );

    // Active-low set drives Q high.
    check_set_forces_q_high: assert property (
        @(posedge CLK) (!SET_B) |=> (Q == 1'b1)
    );

    // Active-low set drives Q_N low.
    check_set_forces_qn_low: assert property (
        @(posedge CLK) (!SET_B) |=> (Q_N == 1'b0)
    );

    // Active-low reset drives Q low when set is inactive.
    check_reset_forces_q_low: assert property (
        @(posedge CLK) (SET_B && !RESET_B) |=> (Q == 1'b0)
    );

    // Active-low reset drives Q_N high when set is inactive.
    check_reset_forces_qn_high: assert property (
        @(posedge CLK) (SET_B && !RESET_B) |=> (Q_N == 1'b1)
    );

    // Set has priority when set and reset are both low.
    check_set_priority_over_reset: assert property (
        @(posedge CLK) (!SET_B && !RESET_B) |=> (Q == 1'b1)
    );

    // With set and reset inactive, Q captures D.
    check_data_capture: assert property (
        @(posedge CLK) (SET_B && RESET_B) |=> (Q == $past(D))
    );

    // With set and reset inactive, Q_N reflects the inverse of D.
    check_data_capture_qn: assert property (
        @(posedge CLK) (SET_B && RESET_B) |=> (Q_N == ~$past(D))
    );

endmodule