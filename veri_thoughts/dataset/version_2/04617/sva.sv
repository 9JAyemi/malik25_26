module top_module_sva (
    input logic clk,
    input logic reset,
    input logic select,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] c,
    input logic [3:0] d,
    input logic [3:0] out
);

    // When select is high, out uses b and the d-c difference.
    check_select_high_formula: assert property (
        @(posedge clk) disable iff (reset)
        select |-> (out == (b + (d - c)))
    );

    // When select is low, out uses c and the c-d difference.
    check_select_low_formula: assert property (
        @(posedge clk) disable iff (reset)
        !select |-> (out == (c + (c - d)))
    );

    // Equal c and d make the difference zero in the select-high case.
    check_zero_diff_select_high: assert property (
        @(posedge clk) disable iff (reset)
        (select && (c == d)) |-> (out == b)
    );

    // Equal c and d make the difference zero in the select-low case.
    check_zero_diff_select_low: assert property (
        @(posedge clk) disable iff (reset)
        (!select && (c == d)) |-> (out == c)
    );

    // Changing a alone never affects out.
    check_a_irrelevant: assert property (
        @(posedge clk) disable iff (reset)
        $past(!reset) && $stable(select) && $stable(b) && $stable(c) && $stable(d) && $changed(a)
        |-> $stable(out)
    );

    // Changing b alone has no effect when select is low.
    check_b_irrelevant_when_select_low: assert property (
        @(posedge clk) disable iff (reset)
        $past(!reset) && !select && $stable(select) && $stable(a) && $stable(c) && $stable(d) && $changed(b)
        |-> $stable(out)
    );

    // With select high, a change in b passes directly to out.
    check_b_delta_when_select_high: assert property (
        @(posedge clk) disable iff (reset)
        $past(!reset) && select && $stable(select) && $stable(a) && $stable(c) && $stable(d) && $changed(b)
        |-> ((out - $past(out)) == (b - $past(b)))
    );

    // With select high, a change in c subtracts directly from out.
    check_c_delta_when_select_high: assert property (
        @(posedge clk) disable iff (reset)
        $past(!reset) && select && $stable(select) && $stable(a) && $stable(b) && $stable(d) && $changed(c)
        |-> ((out - $past(out)) == ($past(c) - c))
    );

    // With select high, a change in d adds directly to out.
    check_d_delta_when_select_high: assert property (
        @(posedge clk) disable iff (reset)
        $past(!reset) && select && $stable(select) && $stable(a) && $stable(b) && $stable(c) && $changed(d)
        |-> ((out - $past(out)) == (d - $past(d)))
    );

    // With select low, a change in c affects out with double weight.
    check_c_delta_when_select_low: assert property (
        @(posedge clk) disable iff (reset)
        $past(!reset) && !select && $stable(select) && $stable(a) && $stable(b) && $stable(d) && $changed(c)
        |-> ((out - $past(out)) == ((c - $past(c)) + (c - $past(c))))
    );

    // With select low, a change in d subtracts directly from out.
    check_d_delta_when_select_low: assert property (
        @(posedge clk) disable iff (reset)
        $past(!reset) && !select && $stable(select) && $stable(a) && $stable(b) && $stable(c) && $changed(d)
        |-> ((out - $past(out)) == ($past(d) - d))
    );

endmodule