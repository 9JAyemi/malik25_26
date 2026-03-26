module ring_counter_sva (
    input logic       Clk,
    input logic [3:0] Q
);

    // Q rotates by one bit on each rising edge.
    check_rotate_vector: assert property (
        @(posedge Clk) 1'b1 |=> (Q == $past({Q[2:0], Q[3]}))
    );

    // Q[3] takes the previous value of Q[2].
    check_q3_from_prev_q2: assert property (
        @(posedge Clk) 1'b1 |=> (Q[3] == $past(Q[2]))
    );

    // Q[2] takes the previous value of Q[1].
    check_q2_from_prev_q1: assert property (
        @(posedge Clk) 1'b1 |=> (Q[2] == $past(Q[1]))
    );

    // Q[1] takes the previous value of Q[0].
    check_q1_from_prev_q0: assert property (
        @(posedge Clk) 1'b1 |=> (Q[1] == $past(Q[0]))
    );

    // Q[0] takes the previous value of Q[3].
    check_q0_from_prev_q3: assert property (
        @(posedge Clk) 1'b1 |=> (Q[0] == $past(Q[3]))
    );

    // Four rotations return Q to its earlier value.
    check_period_four: assert property (
        @(posedge Clk) 1'b1 |=> ##3 (Q == $past(Q, 4))
    );

endmodule