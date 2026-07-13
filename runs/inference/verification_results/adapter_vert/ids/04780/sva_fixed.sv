module top_module_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic out_final,
    input logic xor1_out,
    input logic xor2_out,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (a) != (b) |-> (xor1_out) ;endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk_in_1) (c) != (d) |-> (xor2_out) ;endproperty
assert property (SyncCheckeotid);

property ValidSynceotid; @(posedge clk_in_1) (xor1_out) && ( xor2_out) |-> (out_final) ;endproperty
assert property (ValidSynceotid);

endmodule