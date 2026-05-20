module binary_counter_sva (
    input logic AR,
    input logic E,
    input logic Q,
    input logic s_aclk,
    input logic b0,
    input logic b1,
    input logic b1111
);

property ResetSynceotid; @(posedge s_aclk) (AR) |-> Q == 4'b0 ; endproperty
assert property (ResetSynceotid);

property SyncCheckeotid; @(posedge s_aclk) (AR) != 1'b1 &&  (E) |-> Q == (Q == 4'b1111) ? 4'b0 : Q + 1; endproperty
assert property (SyncCheckeotid);

endmodule