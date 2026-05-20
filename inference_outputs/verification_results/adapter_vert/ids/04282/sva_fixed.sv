module my_module_sva (
    input logic Y,
    input logic and0_out,
    input logic and1_out,
    input logic and2_out,
    input logic nor0_out_Y,
    input logic clk_in_13
);

property SyncCheckeotid; @(posedge clk_in_13) (Y) |-> (and0_out) && (and1_out) && (and2_out) && (nor0_out_Y);endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_in_13) (and0_out) && (and1_out) && (and2_out) |-> (Y) ;endproperty
assert property (SyncCheckeotid_2);

property SyncCheckeotid_3; @(posedge clk_in_13) (and1_out) && (and2_out) |-> (nor0_out_Y); endproperty
assert property (SyncCheckeotid_3);

property SyncCheckeotid_4; @(posedge clk_in_13) (and0_out) && (and1_out) && (and2_out) && (nor0_out_Y) |-> (Y); endproperty
assert property (SyncCheckeotid_4);

endmodule