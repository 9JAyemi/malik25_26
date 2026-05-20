module fifo_wp_inc_sva (
    input logic fifowp_inc,
    input logic free2,
    input logic free3,
    input logic tm_count,
    input logic b0000,
    input logic b0001,
    input logic b0010,
    input logic b0011,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic clk_in_14
);

property SyncIneotid; @(posedge clk_in_14) (free3) &&  (tm_count == 2'b11) |-> fifowp_inc == 4'b0011 ;endproperty
assert property (SyncIneotid);

property ValidWriteeotid; @(posedge clk_in_14) (free2) &&  (tm_count >= 2'b10) |-> fifowp_inc == 4'b0010 ;endproperty
assert property (ValidWriteeotid);

property ValidTxeotid; @(posedge clk_in_14) (tm_count) &&  (tm_count >= 2'b01) |-> fifowp_inc == 4'b0001 ;endproperty
assert property (ValidTxeotid);

property ValidWriteeotid_2; @(posedge clk_in_14) ( !free3 ) &&  ( !free2 ) &&  ( tm_count < 2'b01 ) |-> fifowp_inc == 4'b0000 ;endproperty
assert property (ValidWriteeotid_2);

endmodule