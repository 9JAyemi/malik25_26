module clk_gated_module_sva (
    input logic clk_en,
    input logic clk_en_reg,
    input logic src_clk,
    input logic clk_11,
    input logic clk_en_13,
    input logic clk_en_14,
    input logic clk_en_15,
    input logic clk_en_16
);

property ClockSynceotid; @(posedge src_clk) ( clk_en ) |-> ( clk_en_reg ) ; endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge src_clk) ( clk_en ) &&  (  clk_en_reg  != clk_en ) |-> ( clk_en_13 ) ; endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge src_clk) ( clk_en_13 ) &&  (  clk_en_14  != clk_en_13 ) |-> ( clk_en_15 ) ; endproperty
assert property (ClockSynceotid_3);

property ClockSynceotid_4; @(posedge src_clk) ( clk_en_15 ) &&  (  clk_en_16  != clk_en_15 ) |-> ( clk_11 ) ; endproperty
assert property (ClockSynceotid_4);

endmodule