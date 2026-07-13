module d_to_t_ff_sva (
    input logic clk,
    input logic d,
    input logic q
);

    // q matches the RTL next-state equation from the previous cycle.
    check_q_next_state: assert property (
        @(posedge clk) 1'b1 |=> (q == ($past(d) & $past(q)))
    );

    // A high d forces q high on the next cycle.
    check_d_high_sets_q: assert property (
        @(posedge clk) d |=> q
    );

    // A low q forces q low on the next cycle.
    check_q_low_forces_q_low: assert property (
        @(posedge clk) !q |=> !q
    );

    // A low d with a high q forces q low on the next cycle.
    check_d_low_with_q_high_clears_q: assert property (
        @(posedge clk) (!d && q) |=> !q
    );

endmodule