module control_module_sva (
    input logic input_1,
    input logic input_2,
    input logic input_3,
    input logic input_4,
    input logic input_5,
    input logic input_6,
    input logic input_7,
    input logic input_8,
    input logic output_1,
    input logic b0xx000x,
    input logic clk_reset_19
);

property ResetSynceotid; @(negedge clk_reset_19) (input_1) == (0) |-> output_1 == 0 ; endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(negedge clk_reset_19) (input_1) == (1) |-> output_1 == input_3 ; endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(negedge clk_reset_19) (input_1) == (2) |-> output_1 == input_4 ; endproperty
assert property (ResetSynceotid_3);

property ResetSynceotid_4; @(negedge clk_reset_19) (input_1) == (3) |-> output_1 == input_5 ; endproperty
assert property (ResetSynceotid_4);

property ResetSynceotid_5; @(negedge clk_reset_19) (input_1) == (4) |-> output_1 == input_6 ; endproperty
assert property (ResetSynceotid_5);

property ResetSynceotid_6; @(negedge clk_reset_19) (input_1) == (5) |-> output_1 == input_7 ; endproperty
assert property (ResetSynceotid_6);

property ResetSynceotid_7; @(negedge clk_reset_19) (input_1) == (6) |-> output_1 == input_8 ; endproperty
assert property (ResetSynceotid_7);

property ResetSynceotid_8; @(negedge clk_reset_19) (input_1) == (7) |-> output_1 == input_2 ; endproperty
assert property (ResetSynceotid_8);

property ResetSynceotid_9; @(negedge clk_reset_19) (input_1) != 7'b0xx000x |-> output_1 == 0 ; endproperty
assert property (ResetSynceotid_9);

endmodule