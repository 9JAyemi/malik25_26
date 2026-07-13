module Mux_3x1_bv2_sva (
    input logic clk,
    input logic [1:0] select,
    input logic [31:0] ch_0,
    input logic [31:0] ch_1,
    input logic [31:0] ch_2,
    input logic [31:0] data_out
);

// select 00 drives zero on data_out.
    check_select_zero_drives_zero: assert property (
        @(posedge clk) (select == 2'b00) |-> (data_out == 32'b0)
    );

// select 01 drives ch_0 on data_out.
    check_select_one_drives_ch0: assert property (
        @(posedge clk) (select == 2'b01) |-> (data_out == ch_0)
    );

// select 10 drives ch_1 on data_out.
    check_select_two_drives_ch1: assert property (
        @(posedge clk) (select == 2'b10) |-> (data_out == ch_1)
    );

// select 11 drives ch_2 on data_out.
    check_select_three_drives_ch2: assert property (
        @(posedge clk) (select == 2'b11) |-> (data_out == ch_2)
    );

endmodule
