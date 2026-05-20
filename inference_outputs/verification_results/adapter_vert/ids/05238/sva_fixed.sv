module my_or2_8_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic or_output,
    input logic b0,
    input logic b1,
    input logic clk_in_15
);

property ClockSynceotid; @(posedge clk_in_15) (A) |-> (or_output) ;endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk_in_15) (B) |-> (or_output) ;endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_in_15) (C) != 1'b1 ||  (or_output)  == 1'b0 ;endproperty
assert property (SyncCheckeotid_2);

property SyncCheckeotid_3; @(posedge clk_in_15) (C) == 1'b1 &&  (or_output)  != 1'b0 ;endproperty
assert property (SyncCheckeotid_3);

endmodule