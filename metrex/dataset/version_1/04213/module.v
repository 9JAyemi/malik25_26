module system_axi_iic_0_0_filter
   (detect_stop_b_reg,
    scndry_out,
    scl_rising_edge0,
    scl_rin_d1_reg,
    sda_rin_d1,
    scl_rin_d1,
    scl_i,
    s_axi_aclk,
    sda_i);
  output detect_stop_b_reg;
  output scndry_out;
  output scl_rising_edge0;
  output scl_rin_d1_reg;
  input sda_rin_d1;
  input scl_rin_d1;
  input scl_i;
  input s_axi_aclk;
  input sda_i;

  wire detect_stop_b_reg;
  wire s_axi_aclk;
  wire scl_i;
  wire scl_rin_d1;
  wire scl_rin_d1_reg;
  wire scl_rising_edge0;
  wire scndry_out;
  wire sda_i;
  wire sda_rin_d1;

  system_axi_iic_0_0_debounce SCL_DEBOUNCE
       (.s_axi_aclk(s_axi_aclk),
        .scl_i(scl_i),
        .scl_rin_d1(scl_rin_d1),
        .scl_rin_d1_reg(scl_rin_d1_reg),
        .scl_rising_edge0(scl_rising_edge0));
  system_axi_iic_0_0_debounce_3 SDA_DEBOUNCE
       (.detect_stop_b_reg(detect_stop_b_reg),
        .s_axi_aclk(s_axi_aclk),
        .scndry_out(scndry_out),
        .sda_i(sda_i),
        .sda_rin_d1(sda_rin_d1));
endmodule

module system_axi_iic_0_0_debounce
   (s_axi_aclk,
    scl_i,
    scl_rin_d1,
    scl_rin_d1_reg,
    scl_rising_edge0);
  input s_axi_aclk;
  input scl_i;
  input scl_rin_d1;
  output scl_rin_d1_reg;
  output scl_rising_edge0;

  reg scl_rin_d1_reg;
  reg [1:0] scl_rin_d1_d;
  reg scl_rising_edge0;

  always @(posedge s_axi_aclk) begin
    scl_rin_d1_d <= {scl_rin_d1, scl_rin_d1_d[1]};
    scl_rin_d1_reg <= scl_rin_d1_d[1];
    scl_rising_edge0 <= scl_rin_d1 & ~scl_rin_d1_d[1];
  end
endmodule

module system_axi_iic_0_0_debounce_3
   (detect_stop_b_reg,
    s_axi_aclk,
    scndry_out,
    sda_i,
    sda_rin_d1);
  output detect_stop_b_reg;
  output scndry_out;
  input s_axi_aclk;
  input sda_i;
  input sda_rin_d1;

  reg [2:0] sda_rin_d3;
  reg [2:0] sda_rin_d3_d;
  reg detect_stop_b_reg;
  reg scndry_out;

  always @(posedge s_axi_aclk) begin
    sda_rin_d3_d <= {sda_rin_d1, sda_rin_d3_d[2:1]};
    sda_rin_d3 <= sda_rin_d3_d;
    detect_stop_b_reg <= sda_rin_d3 == 3'b100;
    scndry_out <= sda_rin_d3[2] & ~sda_rin_d3[1];
  end
endmodule