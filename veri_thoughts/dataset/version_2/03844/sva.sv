module multiplexer_4to1_sva (
    input logic [7:0] data_in0,
    input logic [7:0] data_in1,
    input logic [7:0] data_in2,
    input logic [7:0] data_in3,
    input logic [1:0] select,
    input logic [7:0] data_out
);

    // select 00 routes data_in0 to data_out.
    check_select_00_routes_data_in0: assert property (
        @($global_clock) (select == 2'b00) |-> (data_out == data_in0)
    );

    // select 01 routes data_in1 to data_out.
    check_select_01_routes_data_in1: assert property (
        @($global_clock) (select == 2'b01) |-> (data_out == data_in1)
    );

    // select 10 routes data_in2 to data_out.
    check_select_10_routes_data_in2: assert property (
        @($global_clock) (select == 2'b10) |-> (data_out == data_in2)
    );

    // select 11 routes data_in3 to data_out.
    check_select_11_routes_data_in3: assert property (
        @($global_clock) (select == 2'b11) |-> (data_out == data_in3)
    );

endmodule