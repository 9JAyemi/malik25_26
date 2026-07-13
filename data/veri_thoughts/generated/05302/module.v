
module system_axi_uartlite_0_0_pselect_f
(
    ce_expnd_i_3,
    bus2ip_addr_i_reg_2,
    start2,
    bus2ip_addr_i_reg_3
);
  output ce_expnd_i_3;
  input bus2ip_addr_i_reg_2;
  input start2;
  input bus2ip_addr_i_reg_3;

  assign ce_expnd_i_3 = (bus2ip_addr_i_reg_2 & start2 & bus2ip_addr_i_reg_3);

endmodule
