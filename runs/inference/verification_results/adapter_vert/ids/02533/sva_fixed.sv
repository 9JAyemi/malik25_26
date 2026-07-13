module Mux_3x1_bv2_sva (
    input logic ch_0,
    input logic ch_1,
    input logic ch_2,
    input logic data_out,
    input logic select,
    input logic b00,
    input logic b0000000,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic clk_reset_17
);

property ResetSynceotid; @(posedge clk_reset_17) (select) == (2'b00) |-> data_out == 7'b0000000 ; endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge clk_reset_17) (select) == (2'b01) |-> data_out == ch_0 ; endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(posedge clk_reset_17) (select) == (2'b10) |-> data_out == ch_1 ; endproperty
assert property (ResetSynceotid_3);

property ResetSynceotid_4; @(posedge clk_reset_17) (select) == (2'b11) |-> data_out == ch_2 ; endproperty
assert property (ResetSynceotid_4);

endmodule