module my_module_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2,
    input logic X,
    input logic and0_out,
    input logic and1_out,
    input logic or0_out_X,
    input logic clk_in_14
);

property SyncCheckeotid; @(posedge clk_in_14) (A1) && (A2) && (A3) |-> and0_out ;endproperty
assert property (SyncCheckeotid);

property ValidDataeotid; @(posedge clk_in_14) (B1) && (B2) |-> and1_out ;endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk_in_14) (and0_out) || (and1_out) |-> or0_out_X ;endproperty
assert property (ValidDataeotid_2);

property ValidXeotid; @(posedge clk_in_14) (or0_out_X) |->  (X)  ;endproperty
assert property (ValidXeotid);

endmodule