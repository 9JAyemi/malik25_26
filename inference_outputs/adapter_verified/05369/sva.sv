module mux_adder_sva (
    input logic clk,
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

// When sel_mux is 0, out equals the sum of the selected inputs from the first multiplexer.
    check_sel_mux0_sum: assert property (
        @(posedge clk)
        (sel_mux == 1'b0) |-> (out == (mux1_out + mux2_out))
    );

// When sel_mux is 1, out equals the sum of the selected inputs from the second multiplexer.
    check_sel_mux1_sum: assert property (
        @(posedge clk)
        (sel_mux == 1'b1) |-> (out == (mux1_out + mux2_out))
    );

// When sel_mux1 selects data0_mux1, out equals the sum with the selected data2_mux2 value.
    check_mux1_sel0_sum: assert property (
        @(posedge clk)
        (sel_mux1 == 3'b000) |-> (out == (data0_mux1 + mux2_out))
    );

// When sel_mux1 selects data1_mux1, out equals the sum with the selected data1_mux2 value.
    check_mux1_sel1_sum: assert property (
        @(posedge clk)
        (sel_mux1 == 3'b001) |-> (out == (data1_mux1 + mux2_out))
    );

// When sel_mux1 selects data2_mux1, out equals the sum with the selected data2_mux2 value.
    check_mux1_sel2_sum: assert property (
        @(posedge clk)
        (sel_mux1 == 3'b010) |-> (out == (data2_mux1 + mux2_out))
    );

// When sel_mux1 selects data3_mux1, out equals the sum with the selected data3_mux2 value.
    check_mux1_sel3_sum: assert property (
        @(posedge clk)
        (sel_mux1 == 3'b011) |-> (out == (data3_mux1 + mux2_out))
    );

// When sel_mux1 selects data4_mux1, out equals the sum with the selected data4_mux2 value.
    check_mux1_sel4_sum: assert property (
        @(posedge clk)
        (sel_mux1 == 3'b100) |-> (out == (data4_mux1 + mux2_out))
    );

// When sel_mux1 selects data5_mux1, out equals the sum with the selected data5_mux2 value.
    check_mux1_sel5_sum: assert property (
        @(posedge clk)
        (sel_mux1 == 3'b101) |-> (out == (data5_mux1 + mux2_out))
    );

// When sel_mux2 selects data0_mux2, out equals the sum with the selected data0_mux1 value.
    check_mux2_sel0_sum: assert property (
        @(posedge clk)
        (sel_mux2 == 3'b000) |-> (out == (mux1_out + data0_mux2))
    );

// When sel_mux2 selects data1_mux2, out equals the sum with the selected data1_mux1 value.
    check_mux2_sel1_sum: assert property (
        @(posedge clk)
        (sel_mux2 == 3'b001) |-> (out == (mux1_out + data1_mux2))
    );

// When sel_mux2 selects data2_mux2, out equals the sum with the selected data2_mux1 value.
    check_mux2_sel2_sum: assert property (
        @(posedge clk)
        (sel_mux2 == 3'b010) |-> (out == (mux1_out + data2_mux2))
    );

// When sel_mux2 selects data3_mux2, out equals the sum with the selected data3_mux1 value.
    check_mux2_sel3_sum: assert property (
        @(posedge clk)
        (sel_mux2 == 3'b011) |-> (out == (mux1_out + data3_mux2))
    );

// When sel_mux2 selects data4_mux2, out equals the sum with the selected data4_mux1 value.
    check_mux2_sel4_sum: assert property (
        @(posedge clk)
        (sel_mux2 == 3'b100) |-> (out == (mux1_out + data4_mux2))
    );

// When sel_mux2 selects data5_mux2, out equals the sum with the selected data5_mux1 value.
    check_mux2_sel5_sum: assert property (
        @(posedge clk)
        (sel_mux2 == 3'b101) |-> (out == (mux1_out + data5_mux2))
    );

endmodule
