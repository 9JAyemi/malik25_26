module bcd_converter_sva (
    input logic BCD,
    input logic D,
    input logic b0000,
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
    input logic b0001,
    input logic b00010000,
    input logic b00010001,
    input logic b00010010,
    input logic b00010011,
    input logic b00010100,
    input logic b00010101,
    input logic b0010,
    input logic b0011,
    input logic b0100,
    input logic b0101,
    input logic b0110,
    input logic b0111,
    input logic b1000,
    input logic b1001,
    input logic b1010,
    input logic b1011,
    input logic b1100,
    input logic b1101,
    input logic b1110,
    input logic b1111,
    input logic clk_in_11
);

property ZeroSynceotid; @(posedge clk_in_11) (D) == (4'b0000) |-> (BCD) == 8'b00000000 ; endproperty
assert property (ZeroSynceotid);

property OneSynceotid; @(posedge clk_in_11) (D) == (4'b0001) |-> (BCD) == 8'b00000001 ; endproperty
assert property (OneSynceotid);

property TwoSynceotid; @(posedge clk_in_11) (D) == (4'b0010) |-> (BCD) == 8'b00000010 ; endproperty
assert property (TwoSynceotid);

property ThreeSynceotid; @(posedge clk_in_11) (D) == (4'b0011) |-> (BCD) == 8'b00000011 ; endproperty
assert property (ThreeSynceotid);

property FourSynceotid; @(posedge clk_in_11) (D) == (4'b0100) |-> (BCD) == 8'b00000100 ; endproperty
assert property (FourSynceotid);

property FiveSynceotid; @(posedge clk_in_11) (D) == (4'b0101) |-> (BCD) == 8'b00000101 ; endproperty
assert property (FiveSynceotid);

property SixSynceotid; @(posedge clk_in_11) (D) == (4'b0110) |-> (BCD) == 8'b00000110 ; endproperty
assert property (SixSynceotid);

property SevenSynceotid; @(posedge clk_in_11) (D) == (4'b0111) |-> (BCD) == 8'b00000111 ; endproperty
assert property (SevenSynceotid);

property EightSynceotid; @(posedge clk_in_11) (D) == (4'b1000) |-> (BCD) == 8'b00001000 ; endproperty
assert property (EightSynceotid);

property NineSynceotid; @(posedge clk_in_11) (D) == (4'b1001) |-> (BCD) == 8'b00001001 ; endproperty
assert property (NineSynceotid);

property TenSynceotid; @(posedge clk_in_11) (D) == (4'b1010) |-> (BCD) == 8'b00010000 ; endproperty
assert property (TenSynceotid);

property ElevenSynceotid; @(posedge clk_in_11) (D) == (4'b1011) |-> (BCD) == 8'b00010001 ; endproperty
assert property (ElevenSynceotid);

property TwnenineSynceotid; @(posedge clk_in_11) (D) == (4'b1100) |-> (BCD) == 8'b00010010 ; endproperty
assert property (TwnenineSynceotid);

property enneSynceotid; @(posedge clk_in_11) (D) == (4'b1101) |-> (BCD) == 8'b00010011 ; endproperty
assert property (enneSynceotid);

property enneSynceotid_2; @(posedge clk_in_11) (D) == (4'b1110) |-> (BCD) == 8'b00010100 ; endproperty
assert property (enneSynceotid_2);

property enneSynceotid_3; @(posedge clk_in_11) (D) == (4'b1111) |-> (BCD) == 8'b00010101 ; endproperty
assert property (enneSynceotid_3);

endmodule