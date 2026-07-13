module sync3_1_sva (
    input logic clk,
    input logic d,
    input logic q,
    input logic q1,
    input logic c_q1,
    input logic c_q2,
    input logic c_q3
);

    // q1 captures d on each rising clock edge.
    check_q1_captures_d: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> (q1 == $past(d))
    );

    // c_q1 captures the previous q1 value.
    check_c_q1_captures_q1: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> (c_q1 == $past(q1))
    );

    // c_q2 captures the previous c_q1 value.
    check_c_q2_captures_c_q1: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> (c_q2 == $past(c_q1))
    );

    // c_q3 captures the previous c_q2 value.
    check_c_q3_captures_c_q2: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> (c_q3 == $past(c_q2))
    );

    // q always reflects c_q3.
    check_q_matches_c_q3: assert property (
        @(posedge clk) disable iff (1'b0)
        (q == c_q3)
    );

    // q is d delayed by four sampled clock edges.
    check_q_is_delayed_d: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> ##3 (q == $past(d,4))
    );

    // A rise on d appears at q four sampled clock edges later.
    check_d_rise_propagates_to_q: assert property (
        @(posedge clk) disable iff (1'b0)
        $rose(d) |=> ##3 $rose(q)
    );

    // A fall on d appears at q four sampled clock edges later.
    check_d_fall_propagates_to_q: assert property (
        @(posedge clk) disable iff (1'b0)
        $fell(d) |=> ##3 $fell(q)
    );

    // If d is stable across one sample, q is stable four sampled edges later.
    check_d_stability_propagates_to_q: assert property (
        @(posedge clk) disable iff (1'b0)
        $stable(d) |=> ##3 $stable(q)
    );

endmodule