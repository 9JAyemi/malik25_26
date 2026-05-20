module nor_gate_using_nand_sva (
    input logic a,
    input logic b,
    input logic out,
    input logic temp1,
    input logic clk_in_1,
    input logic temp2
);

property SyncOneotid; @(posedge clk_in_1) (a) |-> (temp1) ;endproperty
assert property (SyncOneotid);

property SyncOneotid_2; @(posedge clk_in_1) (b) |-> (temp2) ;endproperty
assert property (SyncOneotid_2);

property ValidOuteotid; @(posedge clk_in_1) (temp1) &&  (temp2) |->  (out) ;endproperty
assert property (ValidOuteotid);

endmodule