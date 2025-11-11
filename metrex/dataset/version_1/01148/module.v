
module PAD_BANK2(PAD, PADIN, PADOUT, PADOEN);
  inout PAD;
  output PADIN;
  input PADOEN;
  input PADOUT;

  reg PAD_drv_reg;
  assign PAD = (PADOEN & ~PADOUT) ? PAD_drv_reg : 1'b1;
  assign PADIN = PAD_drv_reg;

  always @(*) begin
    PAD_drv_reg = PADOUT;
  end

endmodule