module dual_edge_ff_sva (
    input logic clk,
    input logic d,
    input logic q,
    input logic q1,
    input logic q2,
    input logic xor_out
);

    // xor_out is the XOR of q1 and d on posedge samples.
    check_xor_out_function_posedge: assert property (
        @(posedge clk) xor_out == (q1 ^ d)
    );

    // xor_out is the XOR of q1 and d on negedge samples.
    check_xor_out_function_negedge: assert property (
        @(negedge clk) xor_out == (q1 ^ d)
    );

    // q1 holds the d value sampled on the previous posedge.
    check_q1_captures_d: assert property (
        @(posedge clk) !$initstate |-> q1 == $past(d)
    );

    // q2 holds the xor_out value sampled on the previous negedge.
    check_q2_captures_xor_out: assert property (
        @(negedge clk) !$initstate |-> q2 == $past(xor_out)
    );

    // q mirrors q2 on posedge samples.
    check_q_matches_q2_posedge: assert property (
        @(posedge clk) q == q2
    );

    // q mirrors q2 on negedge samples.
    check_q_matches_q2_negedge: assert property (
        @(negedge clk) q == q2
    );

    // q reflects the XOR result captured on the previous negedge.
    check_q_reflects_previous_xor: assert property (
        @(negedge clk) !$initstate |-> q == $past(q1 ^ d)
    );

endmodule