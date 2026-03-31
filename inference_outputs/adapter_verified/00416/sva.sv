module shift_register_sva (
    input logic clk,
    input logic d,
    input logic q
);

// q captures d on the next rising edge.
    check_q_captures_d: assert property (
        @(posedge clk) 1'b1 |=> (q == $past(d))
    );

// q holds its value when d is stable.
    check_q_holds_when_d_stable: assert property (
        @(posedge clk) $stable(d) |=> (q == $past(q))
    );

// q follows the previous two sampled d values.
    check_q_two_cycle_latency: assert property (
        @(posedge clk) 1'b1 |=> ##1 (q == $past(d,2))
    );

endmodule
