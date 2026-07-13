module chatgpt_generate_JC_counter_sva (
    input logic        clk,
    input logic        rst_n,
    input logic [3:0]  Q
);

    // When reset is asserted low, Q must be 0.
    check_reset_forces_zero: assert property (
        @(posedge clk) (!rst_n) |-> (Q == 4'b0000)
    );

    // Upper two bits of Q are always zero when out of reset.
    check_q_upper_bits_zero: assert property (
        @(posedge clk) disable iff (!rst_n) (Q[3:2] == 2'b00)
    );

    // Next Q[1] equals previous Q[0] when out of reset.
    check_q_next1_from_prev0: assert property (
        @(posedge clk) disable iff (!rst_n) $past(rst_n) |-> (Q[1] == $past(Q[0]))
    );

    // Next Q[0] equals previous Q[0] xor previous Q[1] when out of reset.
    check_q_next0_is_prev_xor: assert property (
        @(posedge clk) disable iff (!rst_n) $past(rst_n) |-> (Q[0] == ($past(Q[0]) ^ $past(Q[1])))
    );

    // If previous Q[1] was 1, Q[0] toggles next cycle.
    check_q_lsb_toggle_on_prev_msb1: assert property (
        @(posedge clk) disable iff (!rst_n) ($past(rst_n) && ($past(Q[1]) == 1'b1)) |-> (Q[0] == ~$past(Q[0]))
    );

    // If previous Q[1] was 0, Q[0] holds next cycle.
    check_q_lsb_hold_on_prev_msb0: assert property (
        @(posedge clk) disable iff (!rst_n) ($past(rst_n) && ($past(Q[1]) == 1'b0)) |-> (Q[0] == $past(Q[0]))
    );

    // Once Q is zero out of reset, it remains zero on the next cycle.
    check_q_zero_absorbing: assert property (
        @(posedge clk) disable iff (!rst_n) (Q == 4'b0000) |=> (Q == 4'b0000)
    );

    // From a nonzero state, next state is not zero (out of reset).
    check_no_spurious_zero_entry: assert property (
        @(posedge clk) disable iff (!rst_n) ($past(rst_n) && ($past(Q[1:0]) != 2'b00)) |-> (Q[1:0] != 2'b00)
    );

    // Parity relation: (next Q[1] ^ next Q[0]) equals previous Q[1].
    check_q_parity_relation: assert property (
        @(posedge clk) disable iff (!rst_n) $past(rst_n) |-> ((Q[1] ^ Q[0]) == $past(Q[1]))
    );

    // Two-cycle relation: Q[0] equals Q[1] from two cycles ago (out of reset).
    check_two_cycle_lsb_from_prev_msb: assert property (
        @(posedge clk) disable iff (!rst_n) $past(rst_n,2) |-> (Q[0] == $past(Q[1],2))
    );

    // On reset deassertion, Q becomes zero at the first active clock.
    check_q_zero_on_reset_release: assert property (
        @(posedge clk) disable iff (!rst_n) $rose(rst_n) |-> (Q == 4'b0000)
    );

endmodule