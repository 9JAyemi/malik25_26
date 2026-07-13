module counter_sva (
    input logic clk,
    input logic ctr_d,
    input logic rst,
    input logic b0,
    input logic b1,
    input logic ctr_q
);

property ClockSynceotid; @(posedge clk) (ctr_q) |-> ctr_d == ctr_q + 1'b1 ;endproperty
assert property (ClockSynceotid);

property ResetSynceotid; @(posedge clk) (ctr_q) &&  (  rst == 1 ) |-> ctr_q == 'b0 ;endproperty
assert property (ResetSynceotid);

property SyncCtrleotid; @(posedge clk) (ctr_q) &&  (  rst != 1 )  |-> ctr_q == ctr_d ;endproperty
assert property (SyncCtrleotid);

endmodule