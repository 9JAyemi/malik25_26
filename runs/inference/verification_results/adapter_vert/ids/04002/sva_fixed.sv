module decoder_sva (
    input logic A,
    input logic B,
    input logic O,
    input logic b0000000000000001,
    input logic b0000000000000010,
    input logic b0000000000000100,
    input logic b0000000000001000,
    input logic clk_reset_19
);

property ResetSynceotid; @(negedge clk_reset_19) (A) == (0) && (B) == (0) |-> (O) == 16'b0000000000000001 ; endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(negedge clk_reset_19) (A) == (0) && (B) == (1) |-> (O) == 16'b0000000000000010 ; endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(negedge clk_reset_19) (A) == (1) && (B) == (0) |-> (O) == 16'b0000000000000100 ; endproperty
assert property (ResetSynceotid_3);

property ResetSynceotid_4; @(negedge clk_reset_19) (A) == (1) && (B) == (1) |-> (O) == 16'b0000000000001000 ; endproperty
assert property (ResetSynceotid_4);

endmodule