module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic ctrl,
    input logic [3:0] out_adder,
    input logic [2:0] out_comparator
);

// out_adder is the 4-bit sum of a and b when ctrl is low.
    check_adder_selected: assert property (
        @(posedge clk) disable iff (reset)
        (!ctrl) |-> (out_adder == (a + b))
    );

// out_adder is zero-extended from the comparator result when ctrl is high.
    check_comparator_selected: assert property (
        @(posedge clk) disable iff (reset)
        ctrl |-> (out_adder == {3'b000, out_comparator})
    );

// out_comparator is the comparator result when ctrl is low.
    check_comparator_output_when_adder_selected: assert property (
        @(posedge clk) disable iff (reset)
        (!ctrl) |-> (out_comparator == (a > b ? 3'b100 : (a == b ? 3'b010 : 3'b001)))
    );

// out_comparator is zero when the adder is selected.
    check_zero_when_adder_selected: assert property (
        @(posedge clk) disable iff (reset)
        (!ctrl) |-> (out_comparator == 3'b000)
    );

// When ctrl is low and a is greater than b, out_adder is 100 and out_comparator is 100.
    check_case_a_gt_b: assert property (
        @(posedge clk) disable iff (reset)
        (!ctrl && (a > b)) |-> ((out_adder == 4'b1000) && (out_comparator == 3'b100))
    );

// When ctrl is low and a equals b, out_adder is 010 and out_comparator is 010.
    check_case_a_eq_b: assert property (
        @(posedge clk) disable iff (reset)
        (!ctrl && (a == b)) |-> ((out_adder == 4'b0100) && (out_comparator == 3'b010))
    );

// When ctrl is low and a is less than b, out_adder is 001 and out_comparator is 001.
    check_case_a_lt_b: assert property (
        @(posedge clk) disable iff (reset)
        (!ctrl && (a < b)) |-> ((out_adder == 4'b0001) && (out_comparator == 3'b001))
    );

endmodule
