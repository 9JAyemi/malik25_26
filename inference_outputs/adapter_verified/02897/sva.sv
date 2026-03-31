module mux4_sva (
    input logic clk,
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic sel0,
    input logic sel1,
    input logic [3:0] out
);

// No RTL clock or reset; sample this combinational logic on clk.

    // When sel1 and sel0 are both high, out must equal in3.
    check_sel3_path: assert property (
        @(posedge clk) (sel1 && sel0) |-> (out == in3)
    );

// When sel1 is high and sel0 is low, out must equal in2.
    check_sel2_path: assert property (
        @(posedge clk) (sel1 && !sel0) |-> (out == in2)
    );

// When sel1 is low and sel0 is high, out must equal in1.
    check_sel1_path: assert property (
        @(posedge clk) (!sel1 && sel0) |-> (out == in1)
    );

// When both select bits are low, out must equal in0.
    check_sel0_path: assert property (
        @(posedge clk) (!sel1 && !sel0) |-> (out == in0)
    );

// Out must always match the RTL's full combinational equation.
    check_full_equation: assert property (
        @(posedge clk) out == (sel1 & sel0 ? in3 : sel1 & ~sel0 ? in2 : ~sel1 & sel0 ? in1 : in0)
    );

endmodule
