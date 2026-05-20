module decimal_to_binary_sva (
    input logic in_value,
    input logic out_value,
    input logic b0000,
    input logic b0001,
    input logic b0010,
    input logic b0011,
    input logic b0100,
    input logic b0101,
    input logic b0110,
    input logic b0111,
    input logic b1000,
    input logic b1001,
    input logic bxxxx,
    input logic clk_in_1
);

property ZeroSynceotid; @(posedge clk_in_1) (in_value) == (4'b0000) |-> (out_value) == 4'b0000 ; endproperty
assert property (ZeroSynceotid);

property OneSynceotid; @(posedge clk_in_1) (in_value) == (4'b0001) |-> (out_value) == 4'b0001 ; endproperty
assert property (OneSynceotid);

property TwoSynceotid; @(posedge clk_in_1) (in_value) == (4'b0010) |-> (out_value) == 4'b0010 ; endproperty
assert property (TwoSynceotid);

property ThreeSynceotid; @(posedge clk_in_1) (in_value) == (4'b0011) |-> (out_value) == 4'b0011 ; endproperty
assert property (ThreeSynceotid);

property FourSynceotid; @(posedge clk_in_1) (in_value) == (4'b0100) |-> (out_value) == 4'b0100 ; endproperty
assert property (FourSynceotid);

property FiveSynceotid; @(posedge clk_in_1) (in_value) == (4'b0101) |-> (out_value) == 4'b0101 ; endproperty
assert property (FiveSynceotid);

property SixSynceotid; @(posedge clk_in_1) (in_value) == (4'b0110) |-> (out_value) == 4'b0110 ; endproperty
assert property (SixSynceotid);

property SevenSynceotid; @(posedge clk_in_1) (in_value) == (4'b0111) |-> (out_value) == 4'b0111 ; endproperty
assert property (SevenSynceotid);

property EightSynceotid; @(posedge clk_in_1) (in_value) == (4'b1000) |-> (out_value) == 4'b1000 ; endproperty
assert property (EightSynceotid);

property NineSynceotid; @(posedge clk_in_1) (in_value) == (4'b1001) |-> (out_value) == 4'b1001 ; endproperty
assert property (NineSynceotid);

property ValidInputeotid; @(posedge clk_in_1) (in_value) != 4'bxxxx  |-> (out_value) != 4'bxxxx ; endproperty
assert property (ValidInputeotid);

endmodule