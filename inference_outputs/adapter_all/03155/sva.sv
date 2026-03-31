module math_ops_sva (
    input logic clk,
    input logic reset,
    input logic [1:0] cos,
    input logic [1:0] one,
    input logic [1:0] s1,
    input logic [1:0] s2,
    input logic [1:0] s1_out,
    input logic [1:0] s2_out
);

    // s1_out is the registered sum of the two multiplier outputs from the previous cycle.
    check_s1_out_registered_sum: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (s1_out == $past({({1'b0, cos}) * ({1'b0, s1}), ({1'b0, cos}) * ({1'b0, s2})})))
    );

    // s2_out is the registered sum of the two multiplier outputs from the previous cycle.
    check_s2_out_registered_sum: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (s2_out == $past({({1'b0, (one - cos)}) * ({1'b0, s1}), ({1'b0, cos}) * ({1'b0, s2})})))
    );

    // s1_out matches the previous cycle's registered s1 path.
    check_s1_out_matches_registered_path: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (s1_out == $past(({({1'b0, cos}) * ({1'b0, s1}), 2'b00})))
    );

    // s2_out matches the previous cycle's registered s2 path.
    check_s2_out_matches_registered_path: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (s2_out == $past(({({1'b0, (one - cos)}) * ({1'b0, s1}), ({1'b0, cos}) * ({1'b0, s2})})))
    );

    // s1_out is independent of s2 and only depends on cos and s1 from the previous cycle.
    check_s1_out_independent_of_s2: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> ((s1_out == $past(s1_out)) || ((s1_out != $past(s1_out)) && ($past(s2) == $past(s2, 2)) && ($past(cos) == $past(cos, 2)) && ($past(s1) != $past(s1, 2))))
    );

    // s2_out is independent of s1 and only depends on cos and s2 from the previous cycle.
    check_s2_out_independent_of_s1: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> ((s2_out == $past(s2_out)) || ((s2_out != $past(s2_out)) && ($past(s1) == $past(s1, 2)) && ($past(cos) == $past(cos, 2)) && ($past(s2) != $past(s2, 2))))
    );

    // With cos and s1 stable, s1_out remains stable.
    check_s1_out_stable_when_cos_and_s1_stable: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (($past(cos) == $past(cos, 2)) && ($past(s1) == $past(s1, 2)) && (s1_out == $past(s1_out)))
    );

    // With cos and s2 stable, s2_out remains stable.
    check_s2_out_stable_when_cos_and_s2_stable: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (($past(cos) == $past(cos, 2)) && ($past(s2) == $past(s2, 2)) && (s2_out == $past(s2_out)))
    );

    // With cos and s1 stable, s1_out changes only if s2 changes.
    check_s1_out_changes_only_with_s2: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (($past(cos) == $past(cos, 2)) && ($past(s1) == $past(s1, 2)) && (s1_out != $past(s1_out))) |-> ($past(s2) != $past(s2, 2))
    );

    // With cos and s2 stable, s2_out changes only if s1 changes.
    check_s2_out_changes_only_with_s1: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (($past(cos) == $past(cos, 2)) && ($past(s2) == $past(s2, 2)) && (s2_out != $past(s2_out))) |-> ($past(s1) != $past(s1, 2))
    );

endmodule