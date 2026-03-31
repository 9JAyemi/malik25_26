module mux_adder_sva (
    input logic [2:0] sel_mux1,
    input logic [2:0] sel_mux2,
    input logic [3:0] data0_mux1,
    input logic [3:0] data1_mux1,
    input logic [3:0] data2_mux1,
    input logic [3:0] data3_mux1,
    input logic [3:0] data4_mux1,
    input logic [3:0] data5_mux1,
    input logic [3:0] data0_mux2,
    input logic [3:0] data1_mux2,
    input logic [3:0] data2_mux2,
    input logic [3:0] data3_mux2,
    input logic [3:0] data4_mux2,
    input logic [3:0] data5_mux2,
    input logic sel_mux,
    input logic [3:0] out
);
    // Combinational DUT with no clock/reset; sample on any input edge.

    // When sel_mux==0, out equals the sum of the selected mux1/data pair.
    check_out_when_sel0: assert property (
        @(posedge sel_mux or negedge sel_mux or
          posedge sel_mux1[0] or negedge sel_mux1[0] or
          posedge sel_mux1[1] or negedge sel_mux1[1] or
          posedge sel_mux1[2] or negedge sel_mux1[2] or
          posedge data0_mux1[0] or negedge data0_mux1[0] or
          posedge data0_mux1[1] or negedge data0_mux1[1] or
          posedge data0_mux1[2] or negedge data0_mux1[2] or
          posedge data0_mux1[3] or negedge data0_mux1[3] or
          posedge data1_mux1[0] or negedge data1_mux1[0] or
          posedge data1_mux1[1] or negedge data1_mux1[1] or
          posedge data1_mux1[2] or negedge data1_mux1[2] or
          posedge data1_mux1[3] or negedge data1_mux1[3] or
          posedge data2_mux1[0] or negedge data2_mux1[0] or
          posedge data2_mux1[1] or negedge data2_mux1[1] or
          posedge data2_mux1[2] or negedge data2_mux1[2] or
          posedge data2_mux1[3] or negedge data2_mux1[3] or
          posedge data3_mux1[0] or negedge data3_mux1[0] or
          posedge data3_mux1[1] or negedge data3_mux1[1] or
          posedge data3_mux1[2] or negedge data3_mux1[2] or
          posedge data3_mux1[3] or negedge data3_mux1[3] or
          posedge data4_mux1[0] or negedge data4_mux1[0] or
          posedge data4_mux1[1] or negedge data4_mux1[1] or
          posedge data4_mux1[2] or negedge data4_mux1[2] or
          posedge data4_mux1[3] or negedge data4_mux1[3] or
          posedge data5_mux1[0] or negedge data5_mux1[0] or
          posedge data5_mux1[1] or negedge data5_mux1[1] or
          posedge data5_mux1[2] or negedge data5_mux1[2] or
          posedge data5_mux1[3] or negedge data5_mux1[3])
        (sel_mux == 1'b0) |-> (out == (case (sel_mux1)
            3'b000: data0_mux1;
            3'b001: data1_mux1;
            3'b010: data2_mux1;
            3'b011: data3_mux1;
            3'b100: data4_mux1;
            3'b101: data5_mux1;
            default: 4'b0000;
        endcase))
    );

    // When sel_mux==1, out equals the sum of the selected mux2/data pair.
    check_out_when_sel1: assert property (
        @(posedge sel_mux or negedge sel_mux or
          posedge sel_mux2[0] or negedge sel_mux2[0] or
          posedge sel_mux2[1] or negedge sel_mux2[1] or
          posedge sel_mux2[2] or negedge sel_mux2[2] or
          posedge data0_mux2[0] or negedge data0_mux2[0] or
          posedge data0_mux2[1] or negedge data0_mux2[1] or
          posedge data0_mux2[2] or negedge data0_mux2[2] or
          posedge data0_mux2[3] or negedge data0_mux2[3] or
          posedge data1_mux2[0] or negedge data1_mux2[0] or
          posedge data1_mux2[1] or negedge data1_mux2[1] or
          posedge data1_mux2[2] or negedge data1_mux2[2] or
          posedge data1_mux2[3] or negedge data1_mux2[3] or
          posedge data2_mux2[0] or negedge data2_mux2[0] or
          posedge data2_mux2[1] or negedge data2_mux2[1] or
          posedge data2_mux2[2] or negedge data2_mux2[2] or
          posedge data2_mux2[3] or negedge data2_mux2[3] or
          posedge data3_mux2[0] or negedge data3_mux2[0] or
          posedge data3_mux2[1] or negedge data3_mux2[1] or
          posedge data3_mux2[2] or negedge data3_mux2[2] or
          posedge data3_mux2[3] or negedge data3_mux2[3] or
          posedge data4_mux2[0] or negedge data4_mux2[0] or
          posedge data4_mux2[1] or negedge data4_mux2[1] or
          posedge data4_mux2[2] or negedge data4_mux2[2] or
          posedge data4_mux2[3] or negedge data4_mux2[3] or
          posedge data5_mux2[0] or negedge data5_mux2[0] or
          posedge data5_mux2[1] or negedge data5_mux2[1] or
          posedge data5_mux2[2] or negedge data5_mux2[2] or
          posedge data5_mux2[3] or negedge data5_mux2[3])
        (sel_mux == 1'b1) |-> (out == (case (sel_mux2)
            3'b000: data0_mux2;
            3'b001: data1_mux2;
            3'b010: data2_mux2;
            3'b011: data3_mux2;
            3'b100: data4_mux2;
            3'b101: data5_mux2;
            default: 4'b0000;
        endcase))
    );

    // When sel_mux==0 and sel_mux1==000, out equals data0_mux1.
    check_out_sel0_000: assert property (
        @(posedge sel_mux or negedge sel_mux or
          posedge sel_mux1[0] or negedge sel_mux1[0] or
          posedge data0_mux1[0] or negedge data0_mux1[0] or
          posedge data0_mux1[1] or negedge data0_mux1[1] or
          posedge data0_mux1[2] or negedge data0_mux1[2] or
          posedge data0_mux1[3] or negedge data0_mux1[3])
        (sel_mux == 1'b0 && sel_mux1 == 3'b000) |-> (out == data0_mux1)
    );

    // When sel_mux==0 and sel_mux1==001, out equals data1_mux1.
    check_out_sel0_001: assert property (
        @(posedge sel_mux or negedge sel_mux or
          posedge sel_mux1[0] or negedge sel_mux1[0] or
          posedge data1_mux1[0] or negedge data1_mux1[0] or
          posedge data1_mux1[1] or negedge data1_mux1[1] or
          posedge data1_mux1[2] or negedge data1_mux1[2] or
          posedge data1_mux1[3] or