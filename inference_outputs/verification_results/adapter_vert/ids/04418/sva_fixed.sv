module xor_product_sva (
    input logic adder_output,
    input logic clk,
    input logic in_1,
    input logic in_2,
    input logic reset,
    input logic select,
    input logic xor_input,
    input logic xor_output
);

property ClockSynceotid; @(posedge clk) (select) |-> xor_input == in_2 ; endproperty
assert property (ClockSynceotid);

property SyncAddereotid; @(posedge clk) (select) |-> xor_output == (in_1 + in_2) ^ in_2 ; endproperty
assert property (SyncAddereotid);

property ResetSynceotid; @(posedge clk) (select) &&  (  !reset  ) |-> adder_output == in_1 + in_2 ; endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge clk) (  !select  ) |-> xor_input == in_1 ; endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(posedge clk) (  !select  ) |-> xor_output == (in_1 + in_2) ^ in_1 ; endproperty
assert property (ResetSynceotid_3);

property ResetSynceotid_4; @(posedge clk) (  !select  ) &&  (  !reset  ) |-> adder_output == in_1 + in_2 ; endproperty
assert property (ResetSynceotid_4);

endmodule