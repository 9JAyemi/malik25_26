module decoder_4to16_sva (
    input logic in,
    input logic out,
    input logic b0000,
    input logic b0000000000000001,
    input logic b0000000000000010,
    input logic b0000000000000100,
    input logic b0000000000001000,
    input logic b0000000000010000,
    input logic b0000000000100000,
    input logic b0000000001000000,
    input logic b0000000010000000,
    input logic b0000000100000000,
    input logic b0000001000000000,
    input logic b0000010000000000,
    input logic b0000100000000000,
    input logic b0001,
    input logic b0001000000000000,
    input logic b0010,
    input logic b0010000000000000,
    input logic b0011,
    input logic b0100,
    input logic b0100000000000000,
    input logic b0101,
    input logic b0110,
    input logic b0111,
    input logic b1000,
    input logic b1000000000000000,
    input logic b1001,
    input logic b1010,
    input logic b1011,
    input logic b1100,
    input logic b1101,
    input logic b1110,
    input logic b1111,
    input logic clk_in_1
);

property DecodeOneeotid; @(posedge clk_in_1) (in) == (4'b0000) |-> (out) == 16'b0000000000000001 ; endproperty
assert property (DecodeOneeotid);

property ValidIneotid; @(posedge clk_in_1) (in) == (4'b0001) |-> (out) == 16'b0000000000000010 ; endproperty
assert property (ValidIneotid);

property ValidIneotid_2; @(posedge clk_in_1) (in) == (4'b0010) |-> (out) == 16'b0000000000000100 ; endproperty
assert property (ValidIneotid_2);

property ValidIneotid_3; @(posedge clk_in_1) (in) == (4'b0011) |-> (out) == 16'b0000000000001000 ; endproperty
assert property (ValidIneotid_3);

property ValidIneotid_4; @(posedge clk_in_1) (in) == (4'b0100) |-> (out) == 16'b0000000000010000 ; endproperty
assert property (ValidIneotid_4);

property ValidIneotid_5; @(posedge clk_in_1) (in) == (4'b0101) |-> (out) == 16'b0000000000100000 ; endproperty
assert property (ValidIneotid_5);

property ValidIneotid_6; @(posedge clk_in_1) (in) == (4'b0110) |-> (out) == 16'b0000000001000000 ; endproperty
assert property (ValidIneotid_6);

property ValidIneotid_7; @(posedge clk_in_1) (in) == (4'b0111) |-> (out) == 16'b0000000010000000 ; endproperty
assert property (ValidIneotid_7);

property ValidIneotid_8; @(posedge clk_in_1) (in) == (4'b1000) |-> (out) == 16'b0000000100000000 ; endproperty
assert property (ValidIneotid_8);

property ValidIneotid_9; @(posedge clk_in_1) (in) == (4'b1001) |-> (out) == 16'b0000001000000000 ; endproperty
assert property (ValidIneotid_9);

property ValidIneotid_10; @(posedge clk_in_1) (in) == (4'b1010) |-> (out) == 16'b0000010000000000 ; endproperty
assert property (ValidIneotid_10);

property ValidIneotid_11; @(posedge clk_in_1) (in) == (4'b1011) |-> (out) == 16'b0000100000000000 ; endproperty
assert property (ValidIneotid_11);

property ValidIneotid_12; @(posedge clk_in_1) (in) == (4'b1100) |-> (out) == 16'b0001000000000000 ; endproperty
assert property (ValidIneotid_12);

property ValidIneotid_13; @(posedge clk_in_1) (in) == (4'b1101) |-> (out) == 16'b0010000000000000 ; endproperty
assert property (ValidIneotid_13);

property ValidIneotid_14; @(posedge clk_in_1) (in) == (4'b1110) |-> (out) == 16'b0100000000000000 ; endproperty
assert property (ValidIneotid_14);

property ValidIneotid_15; @(posedge clk_in_1) (in) == (4'b1111) |-> (out) == 16'b1000000000000000 ; endproperty
assert property (ValidIneotid_15);

endmodule