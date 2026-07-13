module three_to_one_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic Y,
    input logic b0,
    input logic b1,
    input logic clk_in_15
);

property ClockSynceotid; @(posedge clk_in_15) (A1) && (A2) |-> (Y) == 1'b1 ;endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_in_15) (A1) && !(A2) && (B1) |-> (Y) == 1'b1 ;endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clk_in_15) !(A1) && (A2) && (B1) |-> (Y) == 1'b1 ;endproperty
assert property (ClockSynceotid_3);

property SyncCheckeotid; @(posedge clk_in_15) !(A1) && !(A2) && !(B1) |-> (Y) == 1'b0 ;endproperty
assert property (SyncCheckeotid);

endmodule