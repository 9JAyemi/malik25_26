module Mux_3x1_bv2_sva #(parameter W = 32) (
    input logic [1:0] select,
    input logic [W-1:0] ch_0,
    input logic [W-1:0] ch_1,
    input logic [W-1:0] ch_2,
    input logic [W-1:0] data_out
);

    // Select 00 drives zero.
    check_select_zero_outputs_zero: assert property (
        @($global_clock) (select == 2'b00) |-> (data_out == {W{1'b0}})
    );

    // Select 01 routes ch_0.
    check_select_one_routes_ch0: assert property (
        @($global_clock) (select == 2'b01) |-> (data_out == ch_0)
    );

    // Select 10 routes ch_1.
    check_select_two_routes_ch1: assert property (
        @($global_clock) (select == 2'b10) |-> (data_out == ch_1)
    );

    // Select 11 routes ch_2.
    check_select_three_routes_ch2: assert property (
        @($global_clock) (select == 2'b11) |-> (data_out == ch_2)
    );

endmodule