module d_flip_flop_assertions (
    input logic clk,
    input logic d,
    input logic q,
    input logic j,
    input logic k
);

    // Sequential logic only, clocked by posedge clk; no reset exists in the RTL.

    // j captures d on the following sampled cycle.
    check_j_captures_d: assert property (
        @(posedge clk) 1'b1 |=> (j == $past(d))
    );

    // k captures the inverse of d on the following sampled cycle.
    check_k_captures_not_d: assert property (
        @(posedge clk) 1'b1 |=> (k == ~$past(d))
    );

    // j and k are complementary after each update.
    check_j_k_complementary: assert property (
        @(posedge clk) 1'b1 |=> (j == ~k)
    );

    // q updates from the previous sampled values of k and q.
    check_q_updates_from_prev_k_xor_prev_q: assert property (
        @(posedge clk) 1'b1 |=> (q == ($past(k) ^ $past(q)))
    );

    // A low previous k leaves q unchanged on the next cycle.
    check_q_holds_when_prev_k_is_low: assert property (
        @(posedge clk) (!k) |=> (q == $past(q))
    );

    // A high previous k toggles q on the next cycle.
    check_q_toggles_when_prev_k_is_high: assert property (
        @(posedge clk) k |=> (q == ~$past(q))
    );

    // A sampled high d drives k low one cycle later.
    check_d_high_drives_k_low: assert property (
        @(posedge clk) d |=> (!k)
    );

    // A sampled low d drives k high one cycle later.
    check_d_low_drives_k_high: assert property (
        @(posedge clk) (!d) |=> k
    );

    // A sampled high d causes q to hold after the k pipeline stage.
    check_d_high_causes_q_hold_after_two_cycles: assert property (
        @(posedge clk) d |=> ##1 (q == $past(q))
    );

    // A sampled low d causes q to toggle after the k pipeline stage.
    check_d_low_causes_q_toggle_after_two_cycles: assert property (
        @(posedge clk) (!d) |=> ##1 (q == ~$past(q))
    );

endmodule