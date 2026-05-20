module sky130_fd_sc_ms__nor3b_sva (
    input logic C_N,
    input logic Y,
    input logic and0_out_Y,
    input logic nor0_out,
    input logic buf0,
    input logic clk_reset_19
);

property ResetSynceotid; @(negedge clk_reset_19) (Y) |-> (and0_out_Y) && (nor0_out); endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(negedge clk_reset_19) (and0_out_Y) |-> (C_N) && (nor0_out); endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(negedge clk_reset_19) (buf0) == (and0_out_Y); endproperty
assert property (ResetSynceotid_3);

endmodule