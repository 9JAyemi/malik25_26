// SVA for video_scaler_sdivhbi family
// Bind these to the DUTs. Concise, high-signal-coverage, focusing on key invariants.

//////////////////////////////////////////////////////////////
// Core unsigned divider: video_scaler_sdivhbi_div_u
//////////////////////////////////////////////////////////////
module sva_video_scaler_sdivhbi_div_u
  #(parameter in0_WIDTH=32, in1_WIDTH=32, out_WIDTH=32) ();

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset behavior (synchronous reset pulse -> next cycle state)
  assert property (@cb $rose(reset) |=> (r_stage == '0 && done == 1'b0));

  // r_stage shift behavior and done tap
  assert property (@cb !ce |=> $stable(r_stage));
  assert property (@cb ce |=> r_stage == {$past(r_stage[in0_WIDTH-1:0]), $past(start)});
  assert property (@cb done == r_stage[in0_WIDTH]);

  // Operand/sign capture only on start
  assert property (@cb !start |=> ($stable(dividend0) && $stable(divisor0) && $stable(sign0)));
  assert property (@cb start |=> (dividend0 == $past(dividend) &&
                                  divisor0  == $past(divisor)  &&
                                  sign0     == $past(sign_i)));
  // sign_o reflects captured sign (one-cycle after start)
  assert property (@cb start |=> (sign_o == $past(sign_i)));

  // Forbid divide-by-zero at acceptance
  assert property (@cb start |-> (divisor != '0));

  // Unsigned correctness at completion (mathematical identities)
  // Guard zero-divisor; remainder bound and reconstruction
  assert property (@cb (done && (divisor0 != '0)) |->
                   ($unsigned(remd) < $unsigned(divisor0)) &&
                   ($unsigned(dividend0) ==
                      ($unsigned(quot) * $unsigned(divisor0)) + $unsigned(remd)));

  // Minimal coverage
  cover property (@cb start ##[1:$] done);
  cover property (@cb done && (remd == '0));

endmodule

bind video_scaler_sdivhbi_div_u
  sva_video_scaler_sdivhbi_div_u #(.in0_WIDTH(in0_WIDTH), .in1_WIDTH(in1_WIDTH), .out_WIDTH(out_WIDTH)) SVA_DIV_U();


//////////////////////////////////////////////////////////////
// Signed wrapper: video_scaler_sdivhbi_div
//////////////////////////////////////////////////////////////
module sva_video_scaler_sdivhbi_div
  #(parameter in0_WIDTH=32, in1_WIDTH=32, out_WIDTH=32) ();

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // CE-gated input staging
  assert property (@cb  ce |=> (start0   == $past(start)));
  assert property (@cb !ce |=>  $stable(start0));

  assert property (@cb  ce |=> (dividend0 == $past(dividend) &&
                                divisor0  == $past(divisor)));
  assert property (@cb !ce |=> ($stable(dividend0) && $stable(divisor0)));

  // Sign encoding and magnitude conversion
  assert property (@cb sign_i ==
                   {dividend0[in0_WIDTH-1] ^ divisor0[in1_WIDTH-1],
                    dividend0[in0_WIDTH-1]});

  assert property (@cb $unsigned(dividend_u) ==
                      (dividend0[in0_WIDTH-1] ? $unsigned(~dividend0 + 1) : $unsigned(dividend0)));
  assert property (@cb $unsigned(divisor_u) ==
                      (divisor0[in1_WIDTH-1] ? $unsigned(~divisor0 + 1) : $unsigned(divisor0)));

  // done is a registered version of done0
  assert property (@cb done == $past(done0));

  // Output sign correction occurs when $past(done0) was high
  assert property (@cb $past(done0) |->
                   (quot == ($past(sign_o[1]) ? (~$past(quot_u) + 1) : $past(quot_u))));
  assert property (@cb $past(done0) |->
                   (remd == ($past(sign_o[0]) ? (~$past(remd_u) + 1) : $past(remd_u))));

  // Coverage: transaction plus a few corner outcomes
  cover property (@cb $rose(start0));
  cover property (@cb $past(done0) && (remd == '0));
  cover property (@cb $past(done0) && ($past(dividend0[in0_WIDTH-1]) ^ $past(divisor0[in1_WIDTH-1]) == quot[out_WIDTH-1]));

endmodule

bind video_scaler_sdivhbi_div
  sva_video_scaler_sdivhbi_div #(.in0_WIDTH(in0_WIDTH), .in1_WIDTH(in1_WIDTH), .out_WIDTH(out_WIDTH)) SVA_DIV();


//////////////////////////////////////////////////////////////
// Optional: top wrapper pass-through coverage
//////////////////////////////////////////////////////////////
module sva_video_scaler_sdivhbi_top
  #(parameter din0_WIDTH=1, din1_WIDTH=1, dout_WIDTH=1) ();

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Start-to-done liveness (eventual completion) — weak cover
  cover property (@cb start ##[1:$] done);

endmodule

bind video_scaler_sdivhbi
  sva_video_scaler_sdivhbi_top #(.din0_WIDTH(din0_WIDTH), .din1_WIDTH(din1_WIDTH), .dout_WIDTH(dout_WIDTH)) SVA_TOP();