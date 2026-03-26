module RegisterAdder_sva (
    input logic [1:0] D,
    input logic [0:0] Q_reg_0,
    input logic [1:0] Q,
    input logic [1:0] Q_reg_2,
    input logic CLK,
    input logic AR
);

    // D is always the 2-bit sum of Q and Q_reg_2.
    check_d_matches_sum: assert property (
        @(posedge CLK) disable iff (!AR) D == (Q + Q_reg_2)
    );

    // D[0] is the sum LSB of the two input words.
    check_d_lsb_matches_input_lsb_sum: assert property (
        @(posedge CLK) disable iff (!AR) D[0] == (Q[0] ^ Q_reg_2[0])
    );

    // D[1] includes the carry from bit 0.
    check_d_msb_matches_input_msb_sum: assert property (
        @(posedge CLK) disable iff (!AR) D[1] == (Q[1] ^ Q_reg_2[1] ^ (Q[0] & Q_reg_2[0]))
    );

    // Q_reg_0 captures the previous cycle's D[0] when not in reset.
    check_q_reg_0_captures_previous_d0: assert property (
        @(posedge CLK) disable iff (!AR) 1'b1 |=> (Q_reg_0[0] == $past(D[0]))
    );

    // After a sampled reset cycle, Q_reg_0 is still 0 on the next active clock.
    check_q_reg_0_zero_after_sampled_reset: assert property (
        @(posedge CLK) disable iff (!AR) $past(!AR) |-> (Q_reg_0[0] == 1'b0)
    );

endmodule