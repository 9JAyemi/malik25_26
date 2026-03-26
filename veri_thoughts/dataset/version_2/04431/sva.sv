module m2_assertions (
    input logic       clk,
    input logic       d,
    input logic [1:0] q
);

    // q[1] captures d on the next sampled clock.
    check_q1_captures_d: assert property (
        @(posedge clk) 1'b1 |=> (q[1] == $past(d))
    );

    // q[0] captures the previous value of q[1].
    check_q0_captures_q1: assert property (
        @(posedge clk) 1'b1 |=> (q[0] == $past(q[1]))
    );

    // q[0] is d delayed by two clock cycles.
    check_q0_two_cycle_delay_of_d: assert property (
        @(posedge clk) 1'b1 |=> ##1 (q[0] == $past(d, 2))
    );

    // q holds the two most recent sampled values of d.
    check_q_is_two_stage_shift_of_d: assert property (
        @(posedge clk) 1'b1 |=> ##1 (q == { $past(d), $past(d, 2) })
    );

endmodule