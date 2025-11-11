// SVA for brush_motor_driver
// Bind inside the DUT to access internal regs (PWM, PWM_out, read_data, etc.)
module brush_motor_driver_sva;

  // ---------------- MCLK domain (Qsys/Avalon) ----------------

  // waitrequest must be 0 always
  assert property (@(posedge csi_MCLK_clk) avs_ctrl_waitrequest == 1'b0);

  // read_data reset
  assert property (@(posedge csi_MCLK_clk)
    rsi_MRST_reset |-> (read_data == 32'b0));

  // Read path: whenever not writing, next cycle read_data reflects address-selected value
  assert property (@(posedge csi_MCLK_clk) disable iff (rsi_MRST_reset)
    !avs_ctrl_write |=> avs_ctrl_readdata ==
      (($past(avs_ctrl_address)==3'd0) ? 32'hEA680003 :
       ($past(avs_ctrl_address)==3'd1) ? $past(PWM_frequent) :
       ($past(avs_ctrl_address)==3'd2) ? $past(PWM_width) :
       ($past(avs_ctrl_address)==3'd3) ? {31'b0,$past(on_off)} :
       ($past(avs_ctrl_address)==3'd4) ? {31'b0,$past(forward_back)} :
       32'b0));

  // While writing, read_data holds its previous value
  assert property (@(posedge csi_MCLK_clk) disable iff (rsi_MRST_reset)
    avs_ctrl_write |=> avs_ctrl_readdata == $past(avs_ctrl_readdata));

  // Byte-enable semantics for writes to PWM_frequent (addr=1) and PWM_width (addr=2)
  genvar i;
  generate
    for (i=0;i<4;i++) begin : be_chk
      localparam int L = i*8;
      assert property (@(posedge csi_MCLK_clk) disable iff (rsi_MRST_reset)
        avs_ctrl_write && (avs_ctrl_address==3'd1) |=> 
          PWM_frequent[L+7:L] ==
            ($past(avs_ctrl_byteenable[i]) ? $past(avs_ctrl_writedata[L+7:L])
                                           : $past(PWM_frequent[L+7:L])));
      assert property (@(posedge csi_MCLK_clk) disable iff (rsi_MRST_reset)
        avs_ctrl_write && (avs_ctrl_address==3'd2) |=> 
          PWM_width[L+7:L] ==
            ($past(avs_ctrl_byteenable[i]) ? $past(avs_ctrl_writedata[L+7:L])
                                           : $past(PWM_width[L+7:L])));
    end
  endgenerate

  // Writes to other addresses do not alter the untouched regs
  assert property (@(posedge csi_MCLK_clk) disable iff (rsi_MRST_reset)
    avs_ctrl_write && (avs_ctrl_address!=3'd1) |=> PWM_frequent == $past(PWM_frequent));
  assert property (@(posedge csi_MCLK_clk) disable iff (rsi_MRST_reset)
    avs_ctrl_write && (avs_ctrl_address!=3'd2) |=> PWM_width == $past(PWM_width));

  // on_off and direction update from writedata[0]
  assert property (@(posedge csi_MCLK_clk) disable iff (rsi_MRST_reset)
    avs_ctrl_write && (avs_ctrl_address==3'd3) |=> on_off == $past(avs_ctrl_writedata[0]));
  assert property (@(posedge csi_MCLK_clk) disable iff (rsi_MRST_reset)
    avs_ctrl_write && (avs_ctrl_address==3'd4) |=> forward_back == $past(avs_ctrl_writedata[0]));

  // ---------------- PWMCLK domain (PWM engine) ----------------

  // Asynchronous reset drives PWM to 0
  assert property (@(posedge rsi_PWMRST_reset) PWM == 32'b0);

  // PWM accumulator update: next value = prev + prev PWM_frequent
  assert property (@(posedge csi_PWMCLK_clk) disable iff (rsi_PWMRST_reset)
    PWM == $past(PWM) + $past(PWM_frequent));

  // PWM_out compares previous PWM vs PWM_width (same-cycle compare realized next cycle)
  assert property (@(posedge csi_PWMCLK_clk) disable iff (rsi_PWMRST_reset)
    PWM_out == (($past(PWM) > $past(PWM_width)) ? 1'b0 : 1'b1));

  // Output mapping and mutual exclusion
  assert property (@(posedge csi_PWMCLK_clk)
    HX == (on_off &  forward_back & PWM_out));
  assert property (@(posedge csi_PWMCLK_clk)
    HY == (on_off & ~forward_back & PWM_out));
  assert property (@(posedge csi_PWMCLK_clk) !(HX & HY));
  assert property (@(posedge csi_PWMCLK_clk) (!on_off) |-> (HX==1'b0 && HY==1'b0));

  // ---------------- Functional coverage (concise, key scenarios) ----------------

  // Bus access coverage
  cover property (@(posedge csi_MCLK_clk) avs_ctrl_write && (avs_ctrl_address==3'd1) && (avs_ctrl_byteenable==4'b1111));
  cover property (@(posedge csi_MCLK_clk) avs_ctrl_write && (avs_ctrl_address==3'd1) && (avs_ctrl_byteenable==4'b0001));
  cover property (@(posedge csi_MCLK_clk) avs_ctrl_write && (avs_ctrl_address==3'd2) && (avs_ctrl_byteenable==4'b1000));
  cover property (@(posedge csi_MCLK_clk) avs_ctrl_write && (avs_ctrl_address inside {3'd3,3'd4}));
  cover property (@(posedge csi_MCLK_clk) !avs_ctrl_write && (avs_ctrl_address inside {3'd0,3'd1,3'd2,3'd3,3'd4}));

  // PWM behavior coverage
  cover property (@(posedge csi_PWMCLK_clk) $rose(PWM_out));
  cover property (@(posedge csi_PWMCLK_clk) $fell(PWM_out));
  cover property (@(posedge csi_PWMCLK_clk) $past(PWM) > PWM); // wrap-around

  // Gating/direction coverage
  cover property (@(posedge csi_PWMCLK_clk) on_off && $changed(forward_back));
  cover property (@(posedge csi_PWMCLK_clk) !on_off && (HX==0) && (HY==0));
endmodule

bind brush_motor_driver brush_motor_driver_sva sva_brush_motor_driver();