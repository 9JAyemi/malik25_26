module mode_selector_sva (
    input logic in,
    input logic mode,
    input logic out,
    input logic b0,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic clk_reset_12
);

property ResetSynceotid; @(negedge clk_reset_12) (mode) == (2'b00) |-> (out) == ({in[2:0], 1'b0}); endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(negedge clk_reset_12) (mode) == (2'b01) |-> (out) == ({1'b0, in[3:1]}); endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(negedge clk_reset_12) (mode) == (2'b10) |-> (out) == (~in); endproperty
assert property (ResetSynceotid_3);

property ResetSynceotid_4; @(negedge clk_reset_12) (mode) == (2'b11) |-> (out) == (in); endproperty
assert property (ResetSynceotid_4);

property ResetSynceotid_5; (mode) != 2'b00 && (mode) != 2'b01 && (mode) != 2'b10 && (mode) != 2'b11 |-> (out) == 4'b0; endproperty
assert property (ResetSynceotid_5);

endmodule