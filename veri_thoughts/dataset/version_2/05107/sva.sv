module dual_edge_triggered_flip_flop_sva (
    input logic clk,
    input logic d,
    input logic q,
    input logic q1,
    input logic q2
);

    // q always mirrors q2 on rising edges.
    check_q_mirrors_q2_posedge: assert property (
        @(posedge clk) q === q2
    );

    // q always mirrors q2 on falling edges.
    check_q_mirrors_q2_negedge: assert property (
        @(negedge clk) q === q2
    );

    // q1 holds the d value from the previous rising edge.
    check_q1_captures_d: assert property (
        @(posedge clk) 1'b1 |=> q1 === $past(d)
    );

    // q2 holds the q1 value seen at the previous falling edge.
    check_q2_captures_q1: assert property (
        @(negedge clk) 1'b1 |=> q2 === $past(q1)
    );

    // q1 and q2 match by the next rising edge.
    check_q1_q2_align_at_posedge: assert property (
        @(posedge clk) 1'b1 |=> q1 === q2
    );

    // q matches q1 by the next rising edge.
    check_q_aligns_with_q1_at_posedge: assert property (
        @(posedge clk) 1'b1 |=> q === q1
    );

    // Externally, q is the previous rising-edge sample of d.
    check_q_matches_previous_d: assert property (
        @(posedge clk) 1'b1 |=> q === $past(d)
    );

endmodule