module bitwise_or_sva (
    input logic a_in,
    input logic b_in,
    input logic clock,
    input logic out
);

property Clockwiseeotid; @(posedge clock) ( a_in ) |-> ( out == a_in | b_in ) ; endproperty
assert property (Clockwiseeotid);

property SyncOr; @(posedge clock) ( b_in ) |-> ( out == a_in | b_in ) ; endproperty
assert property (SyncOr);

property SyncOrEqeotid; @(posedge clock) ( a_in ) &&  (  b_in ) |-> ( out == a_in | b_in ) ; endproperty
assert property (SyncOrEqeotid);

endmodule