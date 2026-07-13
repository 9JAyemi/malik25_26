module decoder_4to16_sva (
    input logic ena,
    input logic in,
    input logic out,
    input logic b0000,
    input logic b0001,
    input logic b0010,
    input logic b0011,
    input logic b0100,
    input logic b0101,
    input logic b0110,
    input logic b0111,
    input logic b0111111111111111,
    input logic b1000,
    input logic b1001,
    input logic b1010,
    input logic b1011,
    input logic b1011111111111111,
    input logic b1100,
    input logic b1101,
    input logic b1101111111111111,
    input logic b1110,
    input logic b1110111111111111,
    input logic b1111,
    input logic b1111011111111111,
    input logic b1111101111111111,
    input logic b1111110111111111,
    input logic b1111111011111111,
    input logic b1111111101111111,
    input logic b1111111110111111,
    input logic b1111111111011111,
    input logic b1111111111101111,
    input logic b1111111111110111,
    input logic b1111111111111011,
    input logic b1111111111111101,
    input logic b1111111111111110,
    input logic b1111111111111111,
    input logic bxxxx,
    input logic bxxxxxxxxxxxxxxxx,
    input logic clk_enable_19
);

property EnableSynceotid; @(posedge clk_enable_19) (in) == (4'b0000) |-> (out) == (ena ? 16'b1111111111111110 : 16'b1111111111111111); endproperty
assert property (EnableSynceotid);

property EnableSynceotid_2; @(posedge clk_enable_19) (in) == (4'b0001) |-> (out) == (ena ? 16'b1111111111111101 : 16'b1111111111111111); endproperty
assert property (EnableSynceotid_2);

property EnableSynceotid_3; @(posedge clk_enable_19) (in) == (4'b0010) |-> (out) == (ena ? 16'b1111111111111011 : 16'b1111111111111111); endproperty
assert property (EnableSynceotid_3);

property EnableSynceotid_4; @(posedge clk_enable_19) (in) == (4'b0011) |-> (out) == (ena ? 16'b1111111111110111 : 16'b1111111111111111); endproperty
assert property (EnableSynceotid_4);

property EnableSynceotid_5; @(posedge clk_enable_19) (in) == (4'b0100) |-> (out) == (ena ? 16'b1111111111101111 : 16'b1111111111111111); endproperty
assert property (EnableSynceotid_5);

property EnableSynceotid_6; @(posedge clk_enable_19) (in) == (4'b0101) |-> (out) == (ena ? 16'b1111111111011111 : 16'b1111111111111111); endproperty
assert property (EnableSynceotid_6);

property EnableSynceotid_7; @(posedge clk_enable_19) (in) == (4'b0110) |-> (out) == (ena ? 16'b1111111110111111 : 16'b1111111111111111); endproperty
assert property (EnableSynceotid_7);

property EnableSynceotid_8; @(posedge clk_enable_19) (in) == (4'b0111) |-> (out) == (ena ? 16'b1111111101111111 : 16'b1111111111111111); endproperty
assert property (EnableSynceotid_8);

property EnableSynceotid_9; @(posedge clk_enable_19) (in) == (4'b1000) |-> (out) == (ena ? 16'b1111111011111111 : 16'b1111111111111111); endproperty
assert property (EnableSynceotid_9);

property EnableSynceotid_10; @(posedge clk_enable_19) (in) == (4'b1001) |-> (out) == (ena ? 16'b1111110111111111 : 16'b1111111111111111); endproperty
assert property (EnableSynceotid_10);

property EnableSynceotid_11; @(posedge clk_enable_19) (in) == (4'b1010) |-> (out) == (ena ? 16'b1111101111111111 : 16'b1111111111111111); endproperty
assert property (EnableSynceotid_11);

property EnableSynceotid_12; @(posedge clk_enable_19) (in) == (4'b1011) |-> (out) == (ena ? 16'b1111011111111111 : 16'b1111111111111111); endproperty
assert property (EnableSynceotid_12);

property EnableSynceotid_13; @(posedge clk_enable_19) (in) == (4'b1100) |-> (out) == (ena ? 16'b1110111111111111 : 16'b1111111111111111); endproperty
assert property (EnableSynceotid_13);

property EnableSynceotid_14; @(posedge clk_enable_19) (in) == (4'b1101) |-> (out) == (ena ? 16'b1101111111111111 : 16'b1111111111111111); endproperty
assert property (EnableSynceotid_14);

property EnableSynceotid_15; @(posedge clk_enable_19) (in) == (4'b1110) |-> (out) == (ena ? 16'b1011111111111111 : 16'b1111111111111111); endproperty
assert property (EnableSynceotid_15);

property EnableSynceotid_16; @(posedge clk_enable_19) (in) == (4'b1111) |-> (out) == (ena ? 16'b0111111111111111 : 16'b1111111111111111); endproperty
assert property (EnableSynceotid_16);

property ValidIneotid; (in) != 4'bxxxx |-> (out) != 16'bxxxxxxxxxxxxxxxx; endproperty
assert property (ValidIneotid);

endmodule