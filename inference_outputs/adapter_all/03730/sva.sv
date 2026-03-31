module d_to_t_ff_sva (
    input logic clk,
    input logic d,
    input logic q
);

    // q follows the previous cycle's d XOR q value.
    check_q_matches_registered_xor: assert property (
        @(posedge clk) disable iff ($initstate)
        q == $past(d ^ q)
    );

    // A high d on the previous cycle forces q high on the current cycle.
    check_prev_d_high_forces_q_high: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(d) |-> q
    );

    // A low d on the previous cycle forces q low on the current cycle.
    check_prev_d_low_forces_q_low: assert property (
        @(posedge clk) disable iff ($initstate)
        !$past(d) |-> !q
    );

    // A high q on the previous cycle keeps q high on the current cycle.
    check_prev_q_high_keeps_q_high: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(q) |-> q
    );

    // A low q on the previous cycle keeps q low on the current cycle.
    check_prev_q_low_keeps_q_low: assert property (
        @(posedge clk) disable iff ($initstate)
        !$past(q) |-> !q
    );

    // A high d with a low q on the previous cycle raises q on the current cycle.
    check_prev_d_high_prev_q_low_raises_q: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(d) && !$past(q)) |-> q
    );

    // A low d with a high q on the previous cycle lowers q on the current cycle.
    check_prev_d_low_prev_q_high_lowers_q: assert property (
        @(posedge clk) disable iff ($initstate)
        (!$past(d) && $past(q)) |-> !q
    );

endmodule