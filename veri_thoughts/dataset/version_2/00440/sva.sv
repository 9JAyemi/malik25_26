module mux4to1_sva (
    input logic clk,
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic sel0,
    input logic sel1,
    input logic out,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // No RTL clock or reset; this combinational mux is sampled on an external clock.

    // sel1=1 and sel0=1 routes in0 to out.
    check_sel11_selects_in0: assert property (
        @(posedge clk) (sel1 && sel0) |-> (out == in0)
    );

    // sel1=1 and sel0=0 routes in1 to out.
    check_sel10_selects_in1: assert property (
        @(posedge clk) (sel1 && !sel0) |-> (out == in1)
    );

    // sel1=0 and sel0=1 routes in2 to out.
    check_sel01_selects_in2: assert property (
        @(posedge clk) (!sel1 && sel0) |-> (out == in2)
    );

    // sel1=0 and sel0=0 routes in3 to out.
    check_sel00_selects_in3: assert property (
        @(posedge clk) (!sel1 && !sel0) |-> (out == in3)
    );

endmodule