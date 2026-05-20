module my_module_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic Y,
    input logic and0_out_Y,
    input logic and1_out_Y,
    input logic nand0_out,
    input logic nand1_out,
    input logic clk_in_15
);

property SyncCheckeotid; @(posedge clk_in_15) (A2) != (A1) |-> (nand0_out) ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_in_15) (B2) != (B1) |-> (nand1_out) ;endproperty
assert property (SyncCheckeotid_2);

property SyncSafeeotid; @(posedge clk_in_15) (nand0_out) && @(posedge clk_in_15) (nand1_out) |-> (and0_out_Y) ;endproperty
assert property (SyncSafeeotid);

property ValidDataeotid; @(posedge clk_in_15) (and0_out_Y) |-> ! (and1_out_Y) ;endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk_in_15)  (and1_out_Y)  |->  (Y)  ;endproperty
assert property (ValidDataeotid_2);

endmodule