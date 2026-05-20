module axi_timer_sva (
    input logic Q,
    input logic bus2ip_addr_i_reg,
    input logic ce_expnd_i_5,
    input logic b0,
    input logic b0000x,
    input logic b0001x,
    input logic b0010x,
    input logic b0011x,
    input logic b0100x,
    input logic b0101x,
    input logic b0110x,
    input logic b0111x,
    input logic b1,
    input logic b1000x,
    input logic b1001x,
    input logic b1010x,
    input logic b1011x,
    input logic b1100x,
    input logic b1101x,
    input logic b1110x,
    input logic b1111x,
    input logic clk_reset_19
);

property ResetSynceotid; @(negedge clk_reset_19) (bus2ip_addr_i_reg) == (5'b0000x) &&  (Q) |-> (ce_expnd_i_5) == 1'b0 ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(negedge clk_reset_19) (bus2ip_addr_i_reg) == (5'b0001x) &&  (Q) |-> (ce_expnd_i_5) == 1'b0 ;endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(negedge clk_reset_19) (bus2ip_addr_i_reg) == (5'b0010x) &&  (Q) |-> (ce_expnd_i_5) == 1'b0 ;endproperty
assert property (ResetSynceotid_3);

property ResetSynceotid_4; @(negedge clk_reset_19) (bus2ip_addr_i_reg) == (5'b0011x) &&  (Q) |-> (ce_expnd_i_5) == 1'b0 ;endproperty
assert property (ResetSynceotid_4);

property ResetSynceotid_5; @(negedge clk_reset_19) (bus2ip_addr_i_reg) == (5'b0100x) &&  (Q) |-> (ce_expnd_i_5) == 1'b0 ;endproperty
assert property (ResetSynceotid_5);

property ResetSynceotid_6; @(negedge clk_reset_19) (bus2ip_addr_i_reg) == (5'b0101x) &&  (Q) |-> (ce_expnd_i_5) == 1'b0 ;endproperty
assert property (ResetSynceotid_6);

property ResetSynceotid_7; @(negedge clk_reset_19) (bus2ip_addr_i_reg) == (5'b0110x) &&  (Q) |-> (ce_expnd_i_5) == 1'b0 ;endproperty
assert property (ResetSynceotid_7);

property ResetSynceotid_8; @(negedge clk_reset_19) (bus2ip_addr_i_reg) == (5'b0111x) &&  (Q) |-> (ce_expnd_i_5) == 1'b0 ;endproperty
assert property (ResetSynceotid_8);

property ResetSynceotid_9; @(negedge clk_reset_19) (bus2ip_addr_i_reg) == (5'b1000x) &&  (Q) |-> (ce_expnd_i_5) == 1'b1 ;endproperty
assert property (ResetSynceotid_9);

property ResetSynceotid_10; @(negedge clk_reset_19) (bus2ip_addr_i_reg) == (5'b1001x) &&  (Q) |-> (ce_expnd_i_5) == 1'b0 ;endproperty
assert property (ResetSynceotid_10);

property ResetSynceotid_11; @(negedge clk_reset_19) (bus2ip_addr_i_reg) == (5'b1010x) &&  (Q) |-> (ce_expnd_i_5) == 1'b0 ;endproperty
assert property (ResetSynceotid_11);

property ResetSynceotid_12; @(negedge clk_reset_19) (bus2ip_addr_i_reg) == (5'b1011x) &&  (Q) |-> (ce_expnd_i_5) == 1'b0 ;endproperty
assert property (ResetSynceotid_12);

property ResetSynceotid_13; @(negedge clk_reset_19) (bus2ip_addr_i_reg) == (5'b1100x) &&  (Q) |-> (ce_expnd_i_5) == 1'b0 ;endproperty
assert property (ResetSynceotid_13);

property ResetSynceotid_14; @(negedge clk_reset_19) (bus2ip_addr_i_reg) == (5'b1101x) &&  (Q) |-> (ce_expnd_i_5) == 1'b0 ;endproperty
assert property (ResetSynceotid_14);

property ResetSynceotid_15; @(negedge clk_reset_19) (bus2ip_addr_i_reg) == (5'b1110x) &&  (Q) |-> (ce_expnd_i_5) == 1'b0 ;endproperty
assert property (ResetSynceotid_15);

property ResetSynceotid_16; @(negedge clk_reset_19) (bus2ip_addr_i_reg) == (5'b1111x) &&  (Q) |-> (ce_expnd_i_5) == 1'b0 ;endproperty
assert property (ResetSynceotid_16);

endmodule