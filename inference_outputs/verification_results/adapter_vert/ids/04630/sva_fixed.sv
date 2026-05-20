module timer_sva (
    input logic clk2,
    input logic cnt,
    input logic wb_clk_i,
    input logic wb_rst_i,
    input logic wb_tgc_o,
    input logic b0
);

property ResetSynceotid; @(posedge wb_clk_i) ( wb_rst_i ) |-> ( cnt == 0 ) ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge wb_clk_i) ( wb_rst_i ) |-> ( clk2 == 1'b0 ) ;endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(posedge wb_clk_i) ( wb_rst_i ) |-> ( wb_tgc_o == 1'b0 ) ;endproperty
assert property (ResetSynceotid_3);

endmodule