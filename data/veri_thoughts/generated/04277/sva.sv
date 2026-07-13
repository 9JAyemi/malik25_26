module chatgpt_generate_JC_counter_sva (
    input logic       clk,
    input logic       rst_n,
    input logic [3:0] Q
);

    // Reset drives Q to zero.
    check_reset_clears_q: assert property (
        @(posedge clk) !rst_n |-> (Q == 4'b0000)
    );

    // A sampled reset keeps the next clocked state at zero.
    check_reset_keeps_zero_next_cycle: assert property (
        @(posedge clk) !rst_n |=> (Q == 4'b0000)
    );

    // Each active clock follows the RTL bit rearrangement.
    check_next_state_rearrangement: assert property (
        @(posedge clk) disable iff (!rst_n)
        1'b1 |=> (Q == {$past(Q[2]), $past(Q[3]), $past(Q[1]), $past(Q[0])})
    );

    // The upper two bits swap on each active clock.
    check_upper_bits_swap: assert property (
        @(posedge clk) disable iff (!rst_n)
        1'b1 |=> (Q[3:2] == {$past(Q[2]), $past(Q[3])})
    );

    // The lower two bits hold their values on each active clock.
    check_lower_bits_hold: assert property (
        @(posedge clk) disable iff (!rst_n)
        1'b1 |=> (Q[1:0] == $past(Q[1:0]))
    );

    // Two active clocks return Q to its earlier value.
    check_two_cycle_repeat: assert property (
        @(posedge clk) disable iff (!rst_n)
        1'b1 |=> ##1 (Q == $past(Q, 2))
    );

endmodule