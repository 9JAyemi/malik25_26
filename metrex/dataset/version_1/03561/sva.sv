// SVA for hybrid_pwm_sd
// Bind this to the DUT to check behavior and provide concise coverage.

module hybrid_pwm_sd_sva
(
  input  logic        clk,
  input  logic        n_reset,
  input  logic [15:0] din,
  input  logic        dout,

  // Tap internal DUT signals
  input  logic [4:0]  pwmcounter,
  input  logic [4:0]  pwmthreshold,
  input  logic [33:0] scaledin,
  input  logic [15:0] sigma,
  input  logic        out
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!n_reset);

  // Basic sanity
  a_no_x:        assert property ( !$isunknown({pwmcounter,pwmthreshold,scaledin,sigma,out,dout}) );
  a_dout_match:  assert property ( dout == out );

  // Asynchronous reset values (sampled at posedge while reset is active)
  a_reset_vals:  assert property ( !n_reset |-> (sigma==16'h0400 && pwmthreshold==5'd16 && pwmcounter==5'd0 && scaledin==34'd0) );

  // Counter increments modulo 32
  a_cnt_inc:     assert property ( $past(n_reset) |-> pwmcounter == (($past(pwmcounter)==5'd31) ? 5'd0 : ($past(pwmcounter)+5'd1)) );

  // Updates only on allowed cycles
  a_scaledin_upd_only_wrap: assert property ( $changed(scaledin)   |-> $past(pwmcounter)==5'd31 );
  a_sigma_upd_only_wrap:    assert property ( $changed(sigma)      |-> $past(pwmcounter)==5'd31 );
  a_thresh_upd_only_wrap:   assert property ( $changed(pwmthreshold)|-> $past(pwmcounter)==5'd31 );
  a_out_changes_only_when:  assert property ( $changed(out)        |-> ($past(pwmcounter)==5'd31 || $past(pwmcounter)==$past(pwmthreshold)) );

  // Exact next-state calculations at wrap (use past values on RHS)
  a_scaledin_next: assert property (
    pwmcounter==5'd31 |=> scaledin == $bits(scaledin)'(34'd134217728 + ({1'b0,$past(din)} * 32'd61440))
  );

  a_sigma_next:    assert property (
    pwmcounter==5'd31 |=> sigma == ($past(scaledin[31:16]) + {5'b00000,$past(sigma[10:0])})
  );

  a_thresh_next:   assert property (
    pwmcounter==5'd31 |=> pwmthreshold == $past(sigma[15:11])
  );

  // PWM output behavior
  a_out_set_on_wrap: assert property ( pwmcounter==5'd31 |=> out==1'b1 );
  a_out_clr_on_thresh: assert property ( (pwmcounter==pwmthreshold && pwmcounter!=5'd31) |=> out==1'b0 );

  // Out stays high from wrap until threshold for non-100% duty
  a_out_high_until_thresh: assert property (
    pwmcounter==5'd31 |=> ((pwmthreshold!=5'd31) |-> ((out==1'b1) until_with (pwmcounter==pwmthreshold)))
  );

  // 100% duty case: stays high until next wrap when threshold==31
  a_out_full_duty: assert property (
    pwmcounter==5'd31 |=> ((pwmthreshold==5'd31) |-> ((out==1'b1) until_with (pwmcounter==5'd31)))
  );

  // Coverage: exercise wrap, extremes and mid duty, and deassert event
  c_wrap:        cover property ( pwmcounter==5'd31 );
  c_thresh_0:    cover property ( (pwmcounter==5'd31) ##1 (pwmthreshold==5'd0)  ##[1:32] (pwmcounter==pwmthreshold) ##1 (out==1'b0) );
  c_thresh_16:   cover property ( (pwmcounter==5'd31) ##1 (pwmthreshold==5'd16) ##[1:32] (pwmcounter==pwmthreshold) ##1 (out==1'b0) );
  c_thresh_31:   cover property ( (pwmcounter==5'd31) ##1 (pwmthreshold==5'd31) ##[1:32] (pwmcounter==5'd31) && out );

endmodule

// Bind into the DUT (add this in a package or a separate file compiled with the DUT)
bind hybrid_pwm_sd hybrid_pwm_sd_sva sva_inst (
  .clk(clk),
  .n_reset(n_reset),
  .din(din),
  .dout(dout),
  .pwmcounter(pwmcounter),
  .pwmthreshold(pwmthreshold),
  .scaledin(scaledin),
  .sigma(sigma),
  .out(out)
);