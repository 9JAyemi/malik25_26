module johnson_counter_and_sva (
    input logic clk,
    input logic counter,
    input logic input_val,
    input logic output_val,
    input logic reset,
    input logic b0000_0000_0000_0000_0000_0000_0000_0000
);

property ResetSynceotid; @(posedge clk) (reset) |-> counter == 64'b0000_0000_0000_0000_0000_0000_0000_0000 ;endproperty
assert property (ResetSynceotid);

property ClockSynceotid; @(posedge clk) ( !reset ) |-> counter == {counter[62:0], counter[63] ^ counter[0]} ;endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk) ( !reset ) |-> output_val == counter & {64{input_val}} ;endproperty
assert property (SyncCheckeotid);

endmodule