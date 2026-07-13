module threshold_module_sva (
    input logic input_value,
    input logic output_value,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic clk_reset_15
);

property ResetOnInputeotid; @(negedge clk_reset_15) (input_value) == (5) |-> (output_value) == 2'b00 ; endproperty
assert property (ResetOnInputeotid);

property ResetSynceotid; @(negedge clk_reset_15) (input_value) >= 10  |-> (output_value) == 2'b10 ; endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(negedge clk_reset_15) (input_value) != 5 && (input_value) < 10  |-> (output_value) == 2'b01 ; endproperty
assert property (ResetSynceotid_2);

endmodule