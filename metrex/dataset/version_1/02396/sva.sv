// SVA checker for d_flip_flop
module dff_sva_chk (input D, VPWR, VGND, VPB, VNB, CLK, Q, Q_N);
  default clocking cb @(posedge CLK); endclocking

  wire pgood = (VPWR===1'b1) && (VGND===1'b0) && (VPB===1'b1) && (VNB===1'b0);

  // Capture behavior (cycle and same-NBA timeslot), and X propagation
  assert property (disable iff (!pgood) Q   === $past(D));
  assert property (disable iff (!pgood) Q_N === ~$past(D));
  assert property (disable iff (!pgood) !$isunknown($sampled(D)) |-> ##0 (Q   === $sampled(D)  && Q_N === ~($sampled(D))));
  assert property (disable iff (!pgood)  $isunknown($sampled(D)) |-> ##0 ($isunknown(Q) && $isunknown(Q_N)));

  // Complement relation must always hold when powered
  assert property (disable iff (!pgood) Q_N === ~Q);

  // Outputs only change on CLK posedge (no glitches when powered)
  assert property (@(posedge Q)   disable iff (!pgood) $rose(CLK));
  assert property (@(negedge Q)   disable iff (!pgood) $rose(CLK));
  assert property (@(posedge Q_N) disable iff (!pgood) $rose(CLK));
  assert property (@(negedge Q_N) disable iff (!pgood) $rose(CLK));

  // Coverage: captures, toggles, holds, X-prop, power-good
  cover property (@(posedge CLK) pgood && $past(D)==0 && D==1 && Q==1 && Q_N==0);
  cover property (@(posedge CLK) pgood && $past(D)==1 && D==0 && Q==0 && Q_N==1);
  cover property (@(posedge CLK) pgood && D==$past(D) && Q==$past(Q) && Q_N==$past(Q_N));
  cover property (@(posedge CLK) pgood && $isunknown(D) ##0 $isunknown(Q) && $isunknown(Q_N));
  cover property ($rose(pgood));
endmodule

bind d_flip_flop dff_sva_chk dff_sva_chk_i (.D(D), .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB), .CLK(CLK), .Q(Q), .Q_N(Q_N));