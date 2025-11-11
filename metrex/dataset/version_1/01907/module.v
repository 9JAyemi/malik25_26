module lpf_module (
   input slowest_sync_clk,
   input dcm_locked,
   input aux_reset_in,
   input mb_debug_sys_rst,
   input ext_reset_in,
   output lpf_int
);

  wire asr_lpf;
  wire lpf_asr;
  wire lpf_exr;
  wire lpf_int0__0;
  wire Q;
  
  reg asr_lpf_reg;
  reg lpf_asr_reg;
  reg lpf_exr_reg;
  
  always @ (posedge slowest_sync_clk) begin
    asr_lpf_reg <= dcm_locked;
    lpf_asr_reg <= asr_lpf_reg;
    lpf_exr_reg <= mb_debug_sys_rst;
  end
  
  assign asr_lpf = asr_lpf_reg;
  assign lpf_asr = lpf_asr_reg;
  assign lpf_exr = lpf_exr_reg;
  
  reg [15:0] Q_reg;
  
  always @ (posedge slowest_sync_clk) begin
    Q_reg <= {Q_reg[14:0], 1'b0};
  end
  
  assign Q = Q_reg[15];
  
  reg [15:0] lpf_int0__0_reg;
  
  always @ (posedge slowest_sync_clk) begin
    lpf_int0__0_reg <= {Q, lpf_asr, dcm_locked, lpf_exr};
  end
  
  assign lpf_int0__0 = lpf_int0__0_reg[0];
  
  reg [15:0] lpf_int_reg;
  
  always @ (posedge slowest_sync_clk) begin
    lpf_int_reg <= lpf_int0__0_reg;
  end
  
  assign lpf_int = lpf_int_reg[0];
  
endmodule