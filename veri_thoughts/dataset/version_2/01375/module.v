module system_auto_cc_0_wr_status_flags_as_82
   (output reg ram_full_fb_i_reg_0,
    output reg [0:0] E,
    output reg s_axi_arready,
    input wire [3:0] gic0_gc0_count_d1_reg_3,
    input wire s_aclk,
    input wire out,
    input wire s_axi_arvalid,
    input wire [0:0] Q,
    input wire [3:0] gnxpm_cdc_rd_pntr_bin_reg_3);

  wire [0:0] E_wire;
  wire [0:0] Q_wire;
  wire [3:0] gic0_gc0_count_d1_reg_wire;
  wire [0:0] gnxpm_cdc_rd_pntr_bin_reg_wire;
  wire out_wire;
  wire ram_full_fb_i;
  wire ram_full_i;
  wire s_aclk_wire;
  wire s_axi_arready_wire;
  wire s_axi_arvalid_wire;

  // Implementing E
  assign E_wire = s_axi_arvalid & ram_full_fb_i;
  always @* begin
    E = E_wire;
  end
  
  // Implementing ram_full_fb_i_reg_0
  assign ram_full_fb_i = s_axi_arvalid & Q & gnxpm_cdc_rd_pntr_bin_reg_3;
  always @* begin
    ram_full_fb_i_reg_0 = ram_full_fb_i;
  end

  // Implementing ram_full_i
  assign ram_full_i = gic0_gc0_count_d1_reg_3;
  
  // Implementing s_axi_arready
  assign s_axi_arready_wire = ram_full_i;
  always @* begin
    s_axi_arready = s_axi_arready_wire;
  end
endmodule