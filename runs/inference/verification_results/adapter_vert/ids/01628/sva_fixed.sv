module debouncer_sva (
    input logic clk,
    input logic debounce_count,
    input logic in,
    input logic out,
    input logic state,
    input logic DEBOUNCE,
    input logic STABLE,
    input logic UNSTABLE
);

property SyncIneotid; @(posedge clk) (in) != (out) |-> state == UNSTABLE ;endproperty
assert property (SyncIneotid);

property SyncCheckeotid; @(posedge clk) (in) != (out) &&  ( debounce_count ) != 0  |-> state == UNSTABLE ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk) (in) != (out) &&  ( debounce_count ) == 0  |-> state == DEBOUNCE && out == in ;endproperty
assert property (SyncCheckeotid_2);

property SyncSafeeotid; @(posedge clk) (in) == (out)  &&  ( state ) == (DEBOUNCE) |-> state == STABLE ;endproperty
assert property (SyncSafeeotid);

endmodule