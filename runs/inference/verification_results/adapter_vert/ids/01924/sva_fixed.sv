module BCD_to_Binary_sva (
    input logic bcd_in,
    input logic bin_out,
    input logic b00000000,
    input logic b00000001,
    input logic b00000010,
    input logic b00000011,
    input logic b00000100,
    input logic b00000101,
    input logic b00000110,
    input logic b00000111,
    input logic b00001000,
    input logic b00001001,
    input logic b1111,
    input logic b11111111,
    input logic clk_in_1,
    input logic d0,
    input logic d1,
    input logic d2,
    input logic d3,
    input logic d4,
    input logic d5,
    input logic d6,
    input logic d7,
    input logic d8,
    input logic d9
);

property BCDtoBinaryeotid; @(posedge clk_in_1) (bcd_in) == (4'd0) |-> (bin_out) == 8'b00000000 ; endproperty
assert property (BCDtoBinaryeotid);

property BCDtoBinaryeotid_2; @(posedge clk_in_1) (bcd_in) == (4'd1) |-> (bin_out) == 8'b00000001 ; endproperty
assert property (BCDtoBinaryeotid_2);

property BCDtoBinaryeotid_3; @(posedge clk_in_1) (bcd_in) == (4'd2) |-> (bin_out) == 8'b00000010 ; endproperty
assert property (BCDtoBinaryeotid_3);

property BCDtoBinaryeotid_4; @(posedge clk_in_1) (bcd_in) == (4'd3) |-> (bin_out) == 8'b00000011 ; endproperty
assert property (BCDtoBinaryeotid_4);

property BCDtoBinaryeotid_5; @(posedge clk_in_1) (bcd_in) == (4'd4) |-> (bin_out) == 8'b00000100 ; endproperty
assert property (BCDtoBinaryeotid_5);

property BCDtoBinaryeotid_6; @(posedge clk_in_1) (bcd_in) == (4'd5) |-> (bin_out) == 8'b00000101 ; endproperty
assert property (BCDtoBinaryeotid_6);

property BCDtoBinaryeotid_7; @(posedge clk_in_1) (bcd_in) == (4'd6) |-> (bin_out) == 8'b00000110 ; endproperty
assert property (BCDtoBinaryeotid_7);

property BCDtoBinaryeotid_8; @(posedge clk_in_1) (bcd_in) == (4'd7) |-> (bin_out) == 8'b00000111 ; endproperty
assert property (BCDtoBinaryeotid_8);

property BCDtoBinaryeotid_9; @(posedge clk_in_1) (bcd_in) == (4'd8) |-> (bin_out) == 8'b00001000 ; endproperty
assert property (BCDtoBinaryeotid_9);

property BCDtoBinaryeotid_10; @(posedge clk_in_1) (bcd_in) == (4'd9) |-> (bin_out) == 8'b00001001 ; endproperty
assert property (BCDtoBinaryeotid_10);

property ValidInputeotid; @(posedge clk_in_1) (bcd_in) != 4'b1111 |-> (bin_out) != 8'b11111111 ; endproperty
assert property (ValidInputeotid);

endmodule