module mux4to1_sva (
    input logic clk,
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic sel0,
    input logic sel1,
    input logic out
);

    // Overall mux equation.
    check_mux_equation: assert property (
        @(posedge clk) out == (sel1 ? (sel0 ? in3 : in2) : (sel0 ? in1 : in0))
    );

    // sel1=0 and sel0=0 selects in0.
    check_select_00_routes_in0: assert property (
        @(posedge clk) (!sel1 && !sel0) |-> (out == in0)
    );

    // sel1=0 and sel0=1 selects in1.
    check_select_01_routes_in1: assert property (
        @(posedge clk) (!sel1 && sel0) |-> (out == in1)
    );

    // sel1=1 and sel0=0 selects in2.
    check_select_10_routes_in2: assert property (
        @(posedge clk) (sel1 && !sel0) |-> (out == in2)
    );

    // sel1=1 and sel0=1 selects in3.
    check_select_11_routes_in3: assert property (
        @(posedge clk) (sel1 && sel0) |-> (out == in3)
    );

endmodule