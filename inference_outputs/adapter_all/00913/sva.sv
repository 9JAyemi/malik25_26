module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic ctrl,
    input logic [3:0] out_adder,
    input logic [2:0] out_comparator
);

    // No RTL clock or reset; clk is an external sampling clock.
    // The DUT is purely combinational and has no registered state.

    // When ctrl is low, the top-level outputs come from the adder path.
    check_ctrl_low_selects_adder: assert property (
        @(posedge clk) disable iff (reset)
        !ctrl |-> ((out_adder == (a + b)) && (out_comparator == 3'b001))
    );

    // When ctrl is high, the top-level outputs come from the comparator path.
    check_ctrl_high_selects_comparator: assert property (
        @(posedge clk) disable iff (reset)
        ctrl |-> ((out_adder == 4'b0000) && (out_comparator == (a > b ? 3'b100 : (a == b ? 3'b010 : 3'b001))))
    );

    // The comparator output always matches the RTL compare expression.
    check_comparator_encoding: assert property (
        @(posedge clk) disable iff (reset)
        out_comparator == (a > b ? 3'b100 : (a == b ? 3'b010 : 3'b001))
    );

    // Equal inputs produce the equal-code result on the comparator output.
    check_equal_inputs_compare_result: assert property (
        @(posedge clk) disable iff (reset)
        (a == b) |-> (out_comparator == 3'b010)
    );

    // Greater-than inputs produce the greater-code result on the comparator output.
    check_greater_inputs_compare_result: assert property (
        @(posedge clk) disable iff (reset)
        (a > b) |-> (out_comparator == 3'b100)
    );

    // Less-than inputs produce the less-code result on the comparator output.
    check_less_inputs_compare_result: assert property (
        @(posedge clk) disable iff (reset)
        (a < b) |-> (out_comparator == 3'b001)
    );

    // The adder output is always zero when ctrl is high.
    check_adder_zero_when_ctrl_high: assert property (
        @(posedge clk) disable iff (reset)
        ctrl |-> (out_adder == 4'b0000)
    );

    // The adder output is the actual sum when ctrl is low.
    check_adder_sum_when_ctrl_low: assert property (
        @(posedge clk) disable iff (reset)
        !ctrl |-> (out_adder == (a + b))
    );

    // The comparator output is always one-hot.
    check_compare_onehot: assert property (
        @(posedge clk) disable iff (reset)
        $onehot(out_comparator)
    );

endmodule