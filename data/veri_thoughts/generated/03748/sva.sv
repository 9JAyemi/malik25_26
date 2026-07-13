module adder_subtractor_assertions (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       control,
    input logic [3:0] out,
    input logic [3:0] sum1,
    input logic [3:0] sum2,
    input logic [3:0] diff1,
    input logic [3:0] diff2
);

    // control is the only clock; the RTL has no reset.

    // sum1 captures the previous sampled addition result.
    check_sum1_captures_add: assert property (
        @(posedge control)
        (!$isunknown($past({a, b}))) |-> (sum1 == $past(a + b))
    );

    // diff1 captures the previous sampled subtraction result.
    check_diff1_captures_sub: assert property (
        @(posedge control)
        (!$isunknown($past({a, b}))) |-> (diff1 == $past(a - b))
    );

    // sum2 captures the previous sampled sum1 value.
    check_sum2_pipelines_sum1: assert property (
        @(posedge control)
        (!$isunknown($past(sum1))) |-> (sum2 == $past(sum1))
    );

    // diff2 captures the previous sampled diff1 value.
    check_diff2_pipelines_diff1: assert property (
        @(posedge control)
        (!$isunknown($past(diff1))) |-> (diff2 == $past(diff1))
    );

    // sum2 matches the addition result from two control edges earlier.
    check_sum2_matches_two_cycle_add: assert property (
        @(posedge control)
        (!$isunknown($past({a, b}, 2))) |-> (sum2 == $past(a + b, 2))
    );

    // diff2 matches the subtraction result from two control edges earlier.
    check_diff2_matches_two_cycle_sub: assert property (
        @(posedge control)
        (!$isunknown($past({a, b}, 2))) |-> (diff2 == $past(a - b, 2))
    );

    // out captures the previous sampled sum2 value.
    check_out_pipelines_sum2: assert property (
        @(posedge control)
        (!$isunknown($past(sum2))) |-> (out == $past(sum2))
    );

    // out matches the addition result from three control edges earlier.
    check_out_matches_three_cycle_add: assert property (
        @(posedge control)
        (!$isunknown($past({a, b}, 3))) |-> (out == $past(a + b, 3))
    );

    // out does not follow the delayed subtraction path when add and subtract differ.
    check_out_not_delayed_sub_when_distinct: assert property (
        @(posedge control)
        (!$isunknown($past({a, b}, 3)) && ($past(a + b, 3) != $past(a - b, 3)))
        |-> (out != $past(a - b, 3))
    );

    // equal delayed sums keep the sampled output stable.
    check_out_stable_when_delayed_sum_stable: assert property (
        @(posedge control)
        (!$isunknown($past({a, b}, 4)) && ($past(a + b, 3) == $past(a + b, 4)))
        |-> $stable(out)
    );

endmodule

bind adder_subtractor adder_subtractor_assertions adder_subtractor_assertions_i (
    .a(a),
    .b(b),
    .control(control),
    .out(out),
    .sum1(sum1),
    .sum2(sum2),
    .diff1(diff1),
    .diff2(diff2)
);