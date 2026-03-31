module dual_d_flip_flop_sva (
    input logic clk,
    input logic reset,
    input logic d_in,
    input logic d_out_1,
    input logic d_out_2
);

    // Active-low reset forces both outputs low.
    check_reset_clears_outputs: assert property (
        @(posedge clk) !reset |-> (d_out_1 == 1'b0 && d_out_2 == 1'b0)
    );

    // d_out_1 captures d_in on the next clock.
    check_d_out_1_captures_d_in: assert property (
        @(posedge clk) disable iff (!reset)
        1'b1 |=> (d_out_1 == $past(d_in))
    );

    // d_out_2 captures the XOR of previous d_out_1 and d_in.
    check_d_out_2_captures_toggle: assert property (
        @(posedge clk) disable iff (!reset)
        1'b1 |=> (d_out_2 == ($past(d_out_1) ^ $past(d_in)))
    );

    // d_out_2 matches the XOR of d_out_1 and d_in from the prior cycle.
    check_d_out_2_matches_registered_xor: assert property (
        @(posedge clk) disable iff (!reset)
        1'b1 |=> (d_out_2 == (d_out_1 ^ $past(d_in)))
    );

    // A high d_out_2 implies the prior d_out_1 was high.
    check_d_out_2_high_implies_prior_d_out_1_high: assert property (
        @(posedge clk) disable iff (!reset)
        d_out_2 |-> $past(d_out_1)
    );

    // A high d_out_2 implies the prior d_in was low.
    check_d_out_2_high_implies_prior_d_in_low: assert property (
        @(posedge clk) disable iff (!reset)
        d_out_2 |-> !$past(d_in)
    );

    // A low d_out_2 implies the prior d_out_1 was low.
    check_d_out_2_low_implies_prior_d_out_1_low: assert property (
        @(posedge clk) disable iff (!reset)
        !d_out_2 |-> !$past(d_out_1)
    );

    // A low d_out_2 implies the prior d_in was high.
    check_d_out_2_low_implies_prior_d_in_high: assert property (
        @(posedge clk) disable iff (!reset)
        !d_out_2 |-> $past(d_in)
    );

endmodule