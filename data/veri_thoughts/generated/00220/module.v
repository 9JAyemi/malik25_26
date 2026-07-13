
module synchronizer_ff_15
   (out,
    rd_rst_asreg_reg ,
    in0,
    s_axi_aclk);
  output out;
  output rd_rst_asreg_reg ;
  input [0:0]in0;
  input s_axi_aclk;

  reg Q_reg;
  wire [0:0]in0;
  wire rd_rst_asreg_reg ;
  wire s_axi_aclk;

  assign out = Q_reg;
  always @(posedge s_axi_aclk) begin
    if (rd_rst_asreg_reg)
      Q_reg <= 1'b0;
    else
      Q_reg <= in0;
  end
  assign rd_rst_asreg_reg = (in0 != Q_reg);
endmodule
