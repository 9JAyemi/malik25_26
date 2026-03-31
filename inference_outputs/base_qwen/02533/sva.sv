```systemverilog
module Mux_3x1_bv2_sva #(parameter W=32)
(
    input wire [1:0] select,
    input wire [W-1:0] ch_0,
    input wire [W-1:0] ch_1,
    input wire [W-1:0] ch_2,
    output reg [W-1:0] data_out
);
    // Mux output is always one of the input channels based on the select signal
    mux_output: assert property (
        @(posedge clk) disable iff (!reset_n) (select == 2'b00) |-> (data_out == {W{1'b0}})
    );
    mux_output_0: assert property (
        @(posedge clk) disable iff (!reset_n) (select == 2'b01) |-> (data_out == ch_0)
    );
    mux_output_1: assert property (
        @(posedge clk) disable iff (!reset_n) (select == 2'b10) |-> (data_out == ch_1)
    );
    mux_output_2: assert property (
        @(posedge clk) disable iff (!reset_n) (select == 2'b11) |-> (data_out == ch_2)
    );
endmodule
```