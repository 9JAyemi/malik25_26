module split_16bit_to_8bit_sva (
    input logic in,
    input logic out_hi,
    input logic out_lo,
    input logic b00,
    input logic b11,
    input logic clk_in_14
);

property ClockSynceotid; @(posedge clk_in_14) (in) |-> (out_hi) ; endproperty
assert property (ClockSynceotid);

property SyncLoadeotid; @(posedge clk_in_14) (in) |-> (out_lo) ; endproperty
assert property (SyncLoadeotid);

property ValidDataeotid; @(posedge clk_in_14) (in) &&  (  (in[15:14] != 2'b00) &&  (in[15:14] != 2'b11) ) |-> (out_hi) ; endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk_in_14) (in) &&  (  (in[15:14] != 2'b00) &&  (in[15:14] != 2'b11) ) |-> (out_lo) ; endproperty
assert property (ValidDataeotid_2);

endmodule