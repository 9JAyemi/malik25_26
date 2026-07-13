module sync2r_1_sva (
    input logic clk,
    input logic preset,
    input logic d,
    input logic q,
    input logic q1,
    input logic q2
);

    // Output mirrors the second register.
    check_output_matches_q2: assert property (
        @(posedge clk) disable iff (preset) q == q2
    );

    // Sampled preset clears both registers and the output.
    check_preset_clears_state: assert property (
        @(posedge clk) preset |-> (!q1 && !q2 && !q)
    );

    // One clock after sampled preset, both stages and output are still low.
    check_post_preset_state_clear: assert property (
        @(posedge clk) preset |=> (!q1 && !q2 && !q)
    );

    // Sampled preset keeps the output low for the next two clocks.
    check_preset_blocks_output_two_clocks: assert property (
        @(posedge clk) preset |=> (!q ##1 !q)
    );

    // The first stage can only be high if d was high on the previous clock.
    check_q1_high_requires_prev_d_high: assert property (
        @(posedge clk) disable iff (preset)
        (!$initstate && !$past($initstate) && q1) |-> $past(d)
    );

    // The second stage can only be high if q1 was high on the previous clock.
    check_q2_high_requires_prev_q1_high: assert property (
        @(posedge clk) disable iff (preset)
        (!$initstate && !$past($initstate) && q2) |-> $past(q1)
    );

    // The output can only be high if d was high two clocks earlier.
    check_q_high_requires_d_high_two_clocks_earlier: assert property (
        @(posedge clk) disable iff (preset)
        (!$initstate && !$past($initstate) && q) |-> $past(d, 2)
    );

    // A low d drives the first stage low on the next clock.
    check_d_low_forces_q1_low_next_clock: assert property (
        @(posedge clk) disable iff (preset) !d |=> !q1
    );

    // A low q1 drives the second stage low on the next clock.
    check_q1_low_forces_q2_low_next_clock: assert property (
        @(posedge clk) disable iff (preset) !q1 |=> !q2
    );

    // A low d drives the output low two clocks later.
    check_d_low_forces_q_low_two_clcks_later: assert property (
        @(posedge clk) disable iff (preset) !d |=> ##1 !q
    );

endmodule