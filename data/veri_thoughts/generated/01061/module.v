
module system_axi_quad_spi_shield_0_wr_status_flags_as
   (\gic0.gc1.count_reg[0] ,
    E,
    \gic0.gc1.count_d2_reg[0] ,
    s_axi_aclk,
    out,
    p_6_in,
    ip2Bus_WrAck_core_reg_1,
    Bus_RNW_reg);
  output \gic0.gc1.count_reg[0] ;
  output [0:0]E;
  input \gic0.gc1.count_d2_reg[0] ;
  input s_axi_aclk;
  input out;
  input p_6_in;
  input ip2Bus_WrAck_core_reg_1;
  input Bus_RNW_reg;

  wire Bus_RNW_reg;
  wire [0:0]E;
  wire \gic0.gc1.count_d2_reg[0] ;
  wire ip2Bus_WrAck_core_reg_1;
  wire out;
  wire p_6_in;
  reg ram_full_fb_i;
  reg ram_full_i;
  reg ram_full_i_reg0;
  reg ram_full_i_reg1;
  reg ram_full_i_reg2;
  wire s_axi_aclk;

  assign \gic0.gc1.count_reg[0]  = ram_full_i_reg2;
  assign E = 1'b0;

   reg [255:0] ram [0:0] ; 

  always @(posedge s_axi_aclk) begin
    if (p_6_in) begin
        ram[0][ip2Bus_WrAck_core_reg_1] <= 1'b1;
    end
  end

  // Flip-flops
  always @(posedge s_axi_aclk) begin
    if (Bus_RNW_reg) begin
      ram_full_i <= out;
      ram_full_fb_i <= 1'b0;
    end
    else begin
      ram_full_fb_i <= ram_full_i;
    end
  end

  always @(posedge s_axi_aclk) begin
    ram_full_i_reg0 <= ram_full_fb_i;
    ram_full_i_reg1 <= ram_full_i_reg0;
    ram_full_i_reg2 <= ram_full_i_reg1;
  end

endmodule