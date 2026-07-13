module binary_converter_sva (
    input logic binary_val,
    input logic input_val,
    input logic b0000,
    input logic b0000000000,
    input logic b0000000001,
    input logic b0000000010,
    input logic b0000000011,
    input logic b0000000100,
    input logic b0000000101,
    input logic b0000000110,
    input logic b0000000111,
    input logic b0000001000,
    input logic b0000001001,
    input logic b0001,
    input logic b0010,
    input logic b0011,
    input logic b0100,
    input logic b0101,
    input logic b0110,
    input logic b0111,
    input logic b1000,
    input logic b1001,
    input logic clk_in_1
);

property ZeroSynceotid; @(posedge clk_in_1) (input_val) == (10'b0000000000) |-> (binary_val) == 4'b0000 ; endproperty
assert property (ZeroSynceotid);

property OneSynceotid; @(posedge clk_in_1) (input_val) == (10'b0000000001) |-> (binary_val) == 4'b0001 ; endproperty
assert property (OneSynceotid);

property TwoSynceotid; @(posedge clk_in_1) (input_val) == (10'b0000000010) |-> (binary_val) == 4'b0010 ; endproperty
assert property (TwoSynceotid);

property ThreeSynceotid; @(posedge clk_in_1) (input_val) == (10'b0000000011) |-> (binary_val) == 4'b0011 ; endproperty
assert property (ThreeSynceotid);

property FourSynceotid; @(posedge clk_in_1) (input_val) == (10'b0000000100) |-> (binary_val) == 4'b0100 ; endproperty
assert property (FourSynceotid);

property FiveSynceotid; @(posedge clk_in_1) (input_val) == (10'b0000000101) |-> (binary_val) == 4'b0101 ; endproperty
assert property (FiveSynceotid);

property SixSynceotid; @(posedge clk_in_1) (input_val) == (10'b0000000110) |-> (binary_val) == 4'b0110 ; endproperty
assert property (SixSynceotid);

property SevenSynceotid; @(posedge clk_in_1) (input_val) == (10'b0000000111) |-> (binary_val) == 4'b0111 ; endproperty
assert property (SevenSynceotid);

property EightSynceotid; @(posedge clk_in_1) (input_val) == (10'b0000001000) |-> (binary_val) == 4'b1000 ; endproperty
assert property (EightSynceotid);

property NineSynceotid; @(posedge clk_in_1) (input_val) == (10'b0000001001) |-> (binary_val) == 4'b1001 ; endproperty
assert property (NineSynceotid);

property ValidInputeotid; @(posedge clk_in_1) (input_val) != 10'b0000000000 && @(posedge clk_in_1) (input_val) != 10'b0000000001 && @(posedge clk_in_1) (input_val) != 10'b0000000010 && @(posedge clk_in_1) (input_val) != 10'b0000000011 && @(posedge clk_in_1) (input_val) != 10'b0000000100 && @(posedge clk_in_1) (input_val) != 10'b0000000101 && @(posedge clk_in_1) (input_val) != 10'b0000000110 && @(posedge clk_in_1) (input_val) != 10'b0000000111 && @(posedge clk_in_1) (input_val) != 10'b0000001000 && @(posedge clk_in_1) (input_val) != 10'b0000001001  |-> (binary_val) == 4'b0000; endproperty
assert property (ValidInputeotid);

endmodule