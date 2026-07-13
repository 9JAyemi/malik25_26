module d_to_t_ff_sva (
    input logic clk,
    input logic d,
    input logic q
);

// q follows the implemented T flip-flop equation on the next clock.
    check_q_next_state: assert property (
        @(posedge clk) 1'b1 |=> (q == ($past(d) & $past(q)))
    );

// A high d with a high q drives q high on the next clock.
    check_q_high_when_d_and_q_high: assert property (
        @(posedge clk) (d && q) |=> q
    );

// A high d with a low q drives q low on the next clock.
    check_q_low_when_d_high_and_q_low: assert property (
        @(posedge clk) (d && !q) |=> !q
    );

// A low d with a high q drives q low on the next clock.
    check_q_low_when_d_low_and_q_high: assert property (
        @(posedge clk) (!d && q) |=> !q
    );

// A low d with a low q leaves q low on the next clock.
    check_q_low_when_d_low_and_q_low: assert property (
        @(posedge clk) (!d && !q) |=> !q
    );

endmodule
