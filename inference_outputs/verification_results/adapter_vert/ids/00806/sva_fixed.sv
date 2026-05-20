module sky130_fd_sc_ls__or4b_sva (
    input logic X,
    input logic or0_out_X,
    input logic clk_osc_15
);

property ValidOnRiseeotid; @(posedge clk_osc_15) (X) == (or0_out_X) ;endproperty
assert property (ValidOnRiseeotid);

property ValidOnRiseeotid_2; @(posedge clk_osc_15) (X) == (or0_out_X) ;endproperty
assert property (ValidOnRiseeotid_2);

property ValidOnRiseeotid_3; @(posedge clk_osc_15) (X) == (or0_out_X) ;endproperty
assert property (ValidOnRiseeotid_3);

endmodule