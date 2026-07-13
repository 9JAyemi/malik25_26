module priority_encoder_sva (
    input logic in,
    input logic out,
    input logic b00,
    input logic b01,
    input logic b0111,
    input logic b10,
    input logic b10110,
    input logic b11,
    input logic b110100,
    input logic b1110000,
    input logic clk_in_1
);

property HighPrioSynceotid; @(posedge clk_in_1) (in) == (7'b1110000) |-> (out) == 2'b00 ; endproperty
assert property (HighPrioSynceotid);

property HighPrioSynceotid_2; @(posedge clk_in_1) (in) == (6'b110100) |-> (out) == 2'b01 ; endproperty
assert property (HighPrioSynceotid_2);

property HighPrioSynceotid_3; @(posedge clk_in_1) (in) == (5'b10110) |-> (out) == 2'b10 ; endproperty
assert property (HighPrioSynceotid_3);

property ValidInputeotid; @(posedge clk_in_1) (in) == (4'b0111) |-> (out) == 2'b11 ; endproperty
assert property (ValidInputeotid);

property SafeStarteotid; @(posedge clk_in_1) (in) != 7'b1110000 && @(posedge clk_in_1) (in) != 6'b110100 && @(posedge clk_in_1) (in) != 5'b10110 && @(posedge clk_in_1) (in) != 4'b0111  |-> (out) == 2'b00; endproperty
assert property (SafeStarteotid);

endmodule