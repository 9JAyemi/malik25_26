module system_auto_cc_0_rd_status_flags_as_19
  (
   output reg out,
   input [1:0] count_d1_reg,
   input m_aclk,
   input rd_rst_reg_reg
   );

  reg ram_empty_fb_i;
  reg ram_empty_i;

  always @ (posedge m_aclk)
    begin
      if (rd_rst_reg_reg)
        ram_empty_fb_i <= 1'b1;
      else
        ram_empty_fb_i <= count_d1_reg[1];
    end

  always @ (posedge m_aclk)
    begin
      if (rd_rst_reg_reg)
        ram_empty_i <= 1'b1;
      else
        ram_empty_i <= count_d1_reg[1];
    end

  always @ (posedge m_aclk)
    begin
      if (rd_rst_reg_reg)
        out <= 1'b1;
      else
        out <= count_d1_reg[1];
    end

endmodule