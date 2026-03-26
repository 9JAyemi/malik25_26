module top_module_sva (
    input logic [2:0] select,
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] data3,
    input logic [3:0] data4,
    input logic [3:0] data5,
    input logic [1:0] op_select,
    input logic [3:0] out
);

    // select 0 routes data0 directly to out.
    check_select0_routes_data0: assert property (
        @($global_clock) (select == 3'd0) |-> (out == data0)
    );

    // select 1 routes data1 directly to out.
    check_select1_routes_data1: assert property (
        @($global_clock) (select == 3'd1) |-> (out == data1)
    );

    // select 2 routes data2 directly to out.
    check_select2_routes_data2: assert property (
        @($global_clock) (select == 3'd2) |-> (out == data2)
    );

    // select 3 routes data3 directly to out.
    check_select3_routes_data3: assert property (
        @($global_clock) (select == 3'd3) |-> (out == data3)
    );

    // select 4 routes data4 directly to out.
    check_select4_routes_data4: assert property (
        @($global_clock) (select == 3'd4) |-> (out == data4)
    );

    // select 5 routes data5 directly to out.
    check_select5_routes_data5: assert property (
        @($global_clock) (select == 3'd5) |-> (out == data5)
    );

    // Invalid select with op 00 produces zero.
    check_invalid_select_op00_zero: assert property (
        @($global_clock) ((select > 3'd5) && (op_select == 2'b00)) |-> (out == 4'b0000)
    );

    // Invalid select with op 01 produces zero.
    check_invalid_select_op01_zero: assert property (
        @($global_clock) ((select > 3'd5) && (op_select == 2'b01)) |-> (out == 4'b0000)
    );

    // Invalid select with op 10 produces 1010.
    check_invalid_select_op10_xor_value: assert property (
        @($global_clock) ((select > 3'd5) && (op_select == 2'b10)) |-> (out == 4'b1010)
    );

    // Invalid select with op 11 produces zero.
    check_invalid_select_op11_zero: assert property (
        @($global_clock) ((select > 3'd5) && (op_select == 2'b11)) |-> (out == 4'b0000)
    );

endmodule