
module system_axi_quad_spi_shield_0_axi_lite_ipif_v3_0_4_pselect_f__parameterized4
   (p_11_out,
    bus2ip_addr_i_reg,
    Q);

  output p_11_out;
  input [4:0] bus2ip_addr_i_reg;
  input Q;

  wire Q;
  wire [4:0] bus2ip_addr_i_reg;
  wire p_11_out;

  assign p_11_out = (bus2ip_addr_i_reg[2] & ~bus2ip_addr_i_reg[0] & bus2ip_addr_i_reg[4] & Q & ~bus2ip_addr_i_reg[3] & bus2ip_addr_i_reg[1]);
endmodule
