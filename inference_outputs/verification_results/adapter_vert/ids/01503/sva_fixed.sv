module fsm_rising_edge_counter_sva (
    input logic clk,
    input logic count,
    input logic d_last,
    input logic in,
    input logic state,
    input logic COUNT,
    input logic IDLE
);

property ClockSynceotid; @(posedge clk) (in) &&  ( !d_last ) |-> state == COUNT ;endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk) (in) &&  ( !d_last ) &&  (  count != 4 ) |-> count == (count + 1) ;endproperty
assert property (ClockSynceotid_2);

property SyncReseteotid; @(posedge clk) (in) &&  ( !d_last ) &&  (  count == 4 ) |-> state == IDLE ;endproperty
assert property (SyncReseteotid);

property SyncCheckeotid; @(posedge clk)  (  !in )  |-> state == IDLE ;endproperty
assert property (SyncCheckeotid);

endmodule