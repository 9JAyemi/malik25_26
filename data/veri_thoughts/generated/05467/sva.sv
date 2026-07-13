module mux4to1_sva (
    input logic clk,
    input logic In0,
    input logic In1,
    input logic In2,
    input logic In3,
    input logic Sel1,
    input logic Sel2,
    input logic Out
);

    // Out routes In0 when the select value is 00.
    check_sel_00_routes_in0: assert property (
        @(posedge clk) ({Sel1, Sel2} == 2'b00) |-> (Out == In0)
    );

    // Out routes In1 when the select value is 01.
    check_sel_01_routes_in1: assert property (
        @(posedge clk) ({Sel1, Sel2} == 2'b01) |-> (Out == In1)
    );

    // Out routes In2 when the select value is 10.
    check_sel_10_routes_in2: assert property (
        @(posedge clk) ({Sel1, Sel2} == 2'b10) |-> (Out == In2)
    );

    // Out routes In3 when the select value is 11.
    check_sel_11_routes_in3: assert property (
        @(posedge clk) ({Sel1, Sel2} == 2'b11) |-> (Out == In3)
    );

endmodule