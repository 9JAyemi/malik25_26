module binary_decoder_3to8_sva (
    input logic in,
    input logic out,
    input logic b000,
    input logic b00000000,
    input logic b00000001,
    input logic b00000010,
    input logic b00000100,
    input logic b00001000,
    input logic b00010000,
    input logic b001,
    input logic b00100000,
    input logic b010,
    input logic b01000000,
    input logic b011,
    input logic b100,
    input logic b10000000,
    input logic b101,
    input logic b110,
    input logic b111,
    input logic clk_reset_19
);

property ResetSynceotid; @(negedge clk_reset_19) (in) == (3'b000) |-> (out) == 8'b00000001 ; endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(negedge clk_reset_19) (in) == (3'b001) |-> (out) == 8'b00000010 ; endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(negedge clk_reset_19) (in) == (3'b010) |-> (out) == 8'b00000100 ; endproperty
assert property (ResetSynceotid_3);

property ResetSynceotid_4; @(negedge clk_reset_19) (in) == (3'b011) |-> (out) == 8'b00001000 ; endproperty
assert property (ResetSynceotid_4);

property ResetSynceotid_5; @(negedge clk_reset_19) (in) == (3'b100) |-> (out) == 8'b00010000 ; endproperty
assert property (ResetSynceotid_5);

property ResetSynceotid_6; @(negedge clk_reset_19) (in) == (3'b101) |-> (out) == 8'b00100000 ; endproperty
assert property (ResetSynceotid_6);

property ResetSynceotid_7; @(negedge clk_reset_19) (in) == (3'b110) |-> (out) == 8'b01000000 ; endproperty
assert property (ResetSynceotid_7);

property ResetSynceotid_8; @(negedge clk_reset_19) (in) == (3'b111) |-> (out) == 8'b10000000 ; endproperty
assert property (ResetSynceotid_8);

property ResetSynceotid_9; @(negedge clk_reset_19) (in) != 3'b000 && @(negedge clk_reset_19) (in) != 3'b001 && @(negedge clk_reset_19) (in) != 3'b010 && @(negedge clk_reset_19) (in) != 3'b011 && @(negedge clk_reset_19) (in) != 3'b100 && @(negedge clk_reset_19) (in) != 3'b101 && @(negedge clk_reset_19) (in) != 3'b110 && @(negedge clk_reset_19) (in) != 3'b111  |-> (out) == 8'b00000000; endproperty
assert property (ResetSynceotid_9);

endmodule