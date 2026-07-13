module binary_adder_sva (
    input logic A,
    input logic B,
    input logic CIN,
    input logic ci,
    input logic or0_out_COUT,
    input logic xor0_out_SUM,
    input logic clk_in_14
);

property SyncAdderCheckeotid; @(posedge clk_in_14) (CIN) |-> (ci) ; endproperty
assert property (SyncAdderCheckeotid);

property ValidAddereotid; @(posedge clk_in_14) (A) != (B) && (CIN) |-> (xor0_out_SUM) ; endproperty
assert property (ValidAddereotid);

property ValidAddereotid_2; @(posedge clk_in_14) (A) != (B) && ! (CIN)  |-> (xor0_out_SUM) ; endproperty
assert property (ValidAddereotid_2);

property ValidAddereotid_3; @(posedge clk_in_14) (A) == (B) && (CIN) |-> (or0_out_COUT) ; endproperty
assert property (ValidAddereotid_3);

property ValidAddereotid_4; @(posedge clk_in_14) (A) == (B) && ! (CIN)  |-> (or0_out_COUT) ; endproperty
assert property (ValidAddereotid_4);

property SyncCheckeotid; @(posedge clk_in_14) (A) != (B) && (CIN) |-> (xor0_out_SUM) ; endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_in_14) (A) != (B) && ! (CIN)  |-> (xor0_out_SUM) ; endproperty
assert property (SyncCheckeotid_2);

property SyncCheckeotid_3; @(posedge clk_in_14) (A) == (B) && (CIN) |-> (or0_out_COUT) ; endproperty
assert property (SyncCheckeotid_3);

property SyncCheckeotid_4; @(posedge clk_in_14) (A) == (B) && ! (CIN)  |-> (or0_out_COUT) ; endproperty
assert property (SyncCheckeotid_4);

endmodule