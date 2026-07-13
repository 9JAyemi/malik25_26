module pipelined_d_ff_assertions (
    input logic clk,
    input logic d,
    input logic q,
    input logic d1,
    input logic d2,
    input logic d3,
    input logic q1,
    input logic q2,
    input logic q3
);

    // d1 captures d on the next clock.
    check_d1_captures_d: assert property (
        @(posedge clk) 1'b1 |=> (d1 == $past(d))
    );

    // d2 captures d1 on the next clock.
    check_d2_captures_d1: assert property (
        @(posedge clk) 1'b1 |=> (d2 == $past(d1))
    );

    // d3 captures d2 on the next clock.
    check_d3_captures_d2: assert property (
        @(posedge clk) 1'b1 |=> (d3 == $past(d2))
    );

    // q1 captures q on the next clock.
    check_q1_captures_q: assert property (
        @(posedge clk) 1'b1 |=> (q1 == $past(q))
    );

    // q2 captures q1 on the next clock.
    check_q2_captures_q1: assert property (
        @(posedge clk) 1'b1 |=> (q2 == $past(q1))
    );

    // q3 captures q2 on the next clock.
    check_q3_captures_q2: assert property (
        @(posedge clk) 1'b1 |=> (q3 == $past(q2))
    );

    // q captures q3 on the next clock.
    check_q_captures_q3: assert property (
        @(posedge clk) 1'b1 |=> (q == $past(q3))
    );

    // d3 is d delayed by three clocks.
    check_d3_three_cycle_delay_of_d: assert property (
        @(posedge clk) 1'b1 |-> ##3 (d3 == $past(d, 3))
    );

    // q3 is q delayed by three clocks.
    check_q3_three_cycle_delay_of_q: assert property (
        @(posedge clk) 1'b1 |-> ##3 (q3 == $past(q, 3))
    );

    // q repeats its sampled value every four clocks.
    check_q_four_cycle_repeat: assert property (
        @(posedge clk) 1'b1 |-> ##4 (q == $past(q, 4))
    );

endmodule