module system_auto_cc_0_wr_status_flags_as_16_sva (
    input logic E,
    input logic out,
    input logic ram_full_fb_i_reg,
    input logic ram_full_fb_i_reg_1,
    input logic s_aclk,
    input logic s_axi_wready,
    input logic b1
);

property ValidWriteeotid; @(posedge s_aclk) (out) |-> ram_full_fb_i_reg == 1'b1 ;endproperty
assert property (ValidWriteeotid);

property ValidWriteeotid_2; @(posedge s_aclk) (out) |->  (E) ;endproperty
assert property (ValidWriteeotid_2);

property ValidWriteeotid_3; @(posedge s_aclk) (out) |->  (ram_full_fb_i_reg_1) ;endproperty
assert property (ValidWriteeotid_3);

property ValidWriteeotid_4; @(posedge s_aclk) (out) |->  (s_axi_wready) ;endproperty
assert property (ValidWriteeotid_4);

endmodule