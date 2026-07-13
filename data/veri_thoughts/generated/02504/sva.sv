module chatgpt_generate_JC_counter_sva (
    input logic              clk,
    input logic              rst_n,
    input logic [63:0]       Q,
    input logic [63:0]       lfsr
);

    ///// Reset behavior /////
    // While reset is asserted, Q and lfsr must be zero.
    check_reset_drives_zero: assert property (
        @(posedge clk) (!rst_n) |-> (Q == 64'h0) && (lfsr == 64'h0)
    );

    // While reset is asserted, Q and lfsr remain stable.
    check_reset_stability: assert property (
        @(posedge clk) (!rst_n) |-> $stable(Q) && $stable(lfsr)
    );

    // On reset deassertion, Q and lfsr are zero on that clock.
    check_deassertion_zero: assert property (
        @(posedge clk) $rose(rst_n) |-> (Q == 64'h0) && (lfsr == 64'h0)
    );

    // After reset release, Q and lfsr remain zero until reset reasserts.
    hold_zero_after_release: assert property (
        @(posedge clk) $rose(rst_n) |-> ((Q == 64'h0) && (lfsr == 64'h0)) until_with (!rst_n)
    );

    ///// Sequential update relations (out of reset) /////
    // When out of reset in consecutive cycles, Q equals previous lfsr.
    check_q_tracks_prev_lfsr: assert property (
        @(posedge clk) disable iff (!rst_n)
            $past(rst_n) |-> (Q == $past(lfsr))
    );

    // When out of reset in consecutive cycles, lfsr updates per shift/XOR polynomial.
    check_lfsr_update_vector: assert property (
        @(posedge clk) disable iff (!rst_n)
            $past(rst_n) |-> (lfsr == { $past(lfsr[62:0]), ($past(lfsr[63]) ^ $past(lfsr[0]) ^ $past(lfsr[1]) ^ $past(lfsr[3])) })
    );

    // Upper bits of lfsr shift left by one when out of reset.
    check_lfsr_shift_upper: assert property (
        @(posedge clk) disable iff (!rst_n)
            $past(rst_n) |-> (lfsr[63:1] == $past(lfsr[62:0]))
    );

    // LSB of lfsr equals XOR of taps 63,0,1,3 from previous cycle when out of reset.
    check_lfsr_lsb_from_taps: assert property (
        @(posedge clk) disable iff (!rst_n)
            $past(rst_n) |-> (lfsr[0] == ($past(lfsr[63]) ^ $past(lfsr[0]) ^ $past(lfsr[1]) ^ $past(lfsr[3])))
    );

    // Zero state is absorbing for lfsr when out of reset.
    check_lfsr_zero_absorbing: assert property (
        @(posedge clk) disable iff (!rst_n)
            ($past(rst_n) && $past(lfsr == 64'h0)) |-> (lfsr == 64'h0)
    );

    // If previous lfsr was zero out of reset, Q must be zero now.
    check_q_zero_when_prev_lfsr_zero: assert property (
        @(posedge clk) disable iff (!rst_n)
            ($past(rst_n) && $past(lfsr == 64'h0)) |-> (Q == 64'h0)
    );

endmodule