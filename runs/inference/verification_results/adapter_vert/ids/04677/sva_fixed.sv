module xor_gate_sva (
    input logic a,
    input logic b,
    input logic w1,
    input logic y,
    input logic b0,
    input logic b1,
    input logic clk_in_17,
    input logic w2,
    input logic w3
);

property SyncXorCheckeotid; @(posedge clk_in_17) ( a ) != ( b ) |-> ( y ) != ( a ); endproperty
assert property (SyncXorCheckeotid);

property SyncCheckeotid; @(posedge clk_in_17) ( a ) != ( b ) |-> ( w1 ) == ( 1'b1 ); endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_in_17) ( a ) != ( b ) |-> ( w2 ) == ( 1'b0 ); endproperty
assert property (SyncCheckeotid_2);

property SyncCheckeotid_3; @(posedge clk_in_17) ( a ) != ( b ) |-> ( w3 ) == ( 1'b0 ); endproperty
assert property (SyncCheckeotid_3);

endmodule