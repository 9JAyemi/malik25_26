module shift_register_sva (
    input logic clk,
    input logic d,
    input logic q
);

    // q reflects the d value sampled two clocks earlier.
    check_q_two_cycle_latency: assert property (
        @(posedge clk) 1'b1 |-> ##2 (q == $past(d, 2))
    );

    // Two consecutive high d values produce two consecutive high q values.
    check_q_two_highs: assert property (
        @(posedge clk) (d ##1 d) |-> (q ##1 q)
    );

    // Two consecutive low d values produce two consecutive low q values.
    check_q_two_lows: assert property (
        @(posedge clk) (!d ##1 !d) |-> (!q ##1 !q)
    );

    // A high d followed by a low d produces a high q followed by a low q.
    check_q_high_then_low: assert property (
        @(posedge clk) (d ##1 !d) |-> (q ##1 !q)
    );

    // A low d followed by a high d produces a low q followed by a high q.
    check_q_low_then_high: assert property (
        @(posedge clk) (!d ##1 d) |-> (!q ##1 q)
    );

endmodule