module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic ctrl,
    input logic [3:0] out_adder,
    input logic [2:0] out_comparator
);

    // out_adder is always the selected adder output.
    check_out_adder_selected: assert property (
        @(posedge clk) disable iff (reset)
        out_adder == (ctrl ? {1'b0, 2'b00} : {4{a[3]}} + {4{b[3]}})
    );

    // out_comparator is always the selected comparator output.
    check_out_comparator_selected: assert property (
        @(posedge clk) disable iff (reset)
        out_comparator == (ctrl ? 3'b000 : (a > b) ? 3'b100 : (a == b) ? 3'b010 : 3'b001)
    );

    // In add mode, out_adder is the 4-bit sum of a and b.
    check_add_mode_sum: assert property (
        @(posedge clk) disable iff (reset)
        !ctrl |-> (out_adder == ({4{a[3]}} + {4{b[3]}}))
    );

    // In comparator mode, out_comparator encodes a > b.
    check_compare_mode_gt: assert property (
        @(posedge clk) disable iff (reset)
        ctrl |-> ((a > b) |-> (out_comparator == 3'b100))
    );

    // In comparator mode, out_comparator encodes a == b.
    check_compare_mode_eq: assert property (
        @(posedge clk) disable iff (reset)
        ctrl |-> ((a == b) |-> (out_comparator == 3'b010))
    );

    // In comparator mode, out_comparator encodes a < b.
    check_compare_mode_lt: assert property (
        @(posedge clk) disable iff (reset)
        ctrl |-> ((a < b) |-> (out_comparator == 3'b001))
    );

endmodule