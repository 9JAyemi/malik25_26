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

    // When sel_mux is low, out is the sum of the selected data0 inputs.
    check_out_sum_data0: assert property (
        @($global_clock)
        (sel_mux == 1'b0) |-> (out == (data0_mux1 + data0_mux2))
    );

    // When sel_mux is high, out is the sum of the selected data1 inputs.
    check_out_sum_data1: assert property (
        @($global_clock)
        (sel_mux == 1'b1) |-> (out == (data1_mux1 + data1_mux2))
    );

    // When sel_mux1 selects data0_mux1, out matches the selected data0 sum.
    check_out_sum_data0_mux1: assert property (
        @($global_clock)
        ((sel_mux == 1'b0) && (sel_mux1 == 3'b000)) |-> (out == (data0_mux1 + data0_mux2))
    );

    // When sel_mux1 selects data1_mux1, out matches the selected data1 sum.
    check_out_sum_data1_mux1: assert property (
        @($global_clock)
        ((sel_mux == 1'b0) && (sel_mux1 == 3'b001)) |-> (out == (data1_mux1 + data1_mux2))
    );

    // When sel_mux1 selects data2_mux1, out matches the selected data2 sum.
    check_out_sum_data2_mux1: assert property (
        @($global_clock)
        ((sel_mux == 1'b0) && (sel_mux1 == 3'b010)) |-> (out == (data2_mux1 + data2_mux2))
    );

    // When sel_mux1 selects data3_mux1, out matches the selected data3 sum.
    check_out_sum_data3_mux1: assert property (
        @($global_clock)
        ((sel_mux == 1'b0) && (sel_mux1 == 3'b011)) |-> (out == (data3_mux1 + data3_mux2))
    );

    // When sel_mux1 selects data4_mux1, out matches the selected data4 sum.
    check_out_sum_data4_mux1: assert property (
        @($global_clock)
        ((sel_mux == 1'b0) && (sel_mux1 == 3'b100)) |-> (out == (data4_mux1 + data4_mux2))
    );

    // When sel_mux1 selects data5_mux1, out matches the selected data5 sum.
    check_out_sum_data5_mux1: assert property (
        @($global_clock)
        ((sel_mux == 1'b0) && (sel_mux1 == 3'b101)) |-> (out == (data5_mux1 + data5_mux2))
    );

    // When sel_mux2 selects data0_mux2, out matches the selected data0 sum.
    check_out_sum_data0_mux2: assert property (
        @($global_clock)
        ((sel_mux == 1'b1) && (sel_mux2 == 3'b000)) |-> (out == (data0_mux1 + data0_mux2))
    );

    // When sel_mux2 selects data1_mux2, out matches the selected data1 sum.
    check_out_sum_data1_mux2: assert property (
        @($global_clock)
        ((sel_mux == 1'b1) && (sel_mux2 == 3'b001)) |-> (out == (data1_mux1 + data1_mux2))
    );

    // When sel_mux2 selects data2_mux2, out matches the selected data2 sum.
    check_out_sum_data2_mux2: assert property (
        @($global_clock)
        ((sel_mux == 1'b1) && (sel_mux2 == 3'b010)) |-> (out == (data2_mux1 + data2_mux2))
    );

    // When sel_mux2 selects data3_mux2, out matches the selected data3 sum.
    check_out_sum_data3_mux2: assert property (
        @($global_clock)
        ((sel_mux == 1'b1) && (sel_mux2 == 3'b011)) |-> (out == (data3_mux1 + data3_mux2))
    );

    // When sel_mux2 selects data4_mux2, out matches the selected data4 sum.
    check_out_sum_data4_mux2: assert property (
        @($global_clock)
        ((sel_mux == 1'b1) && (sel_mux2 == 3'b100)) |-> (out == (data4_mux1 + data4_mux2))
    );

    // When sel_mux2 selects data5_mux2, out matches the selected data5 sum.
    check_out_sum_data5_mux2: assert property (
        @($global_clock)
        ((sel_mux == 1'b1) && (sel_mux2 == 3'b101)) |-> (out == (data5_mux1 + data5_mux2))
    );

endmodule