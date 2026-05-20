module fifo_buffer_sva (
    input logic aclr,
    input logic clk,
    input logic dout,
    input logic mem,
    input logic b0,
    input logic h0
);

property ResetSynceotid; @(posedge clk) (aclr) |-> mem == 6'h0 ;endproperty
assert property (ResetSynceotid);

property SyncIneotid; @(posedge clk) (aclr) |-> dout == 1'b0 ;endproperty
assert property (SyncIneotid);

property SyncIneotid_2; @(posedge clk) ( !aclr ) |-> mem == mem ;endproperty
assert property (SyncIneotid_2);

property SyncIneotid_3; @(posedge clk) ( !aclr ) |-> dout == mem ;endproperty
assert property (SyncIneotid_3);

endmodule