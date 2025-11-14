// SVA checkers for mult_16x16 and MULT
// Focus: correctness, X-propagation, latency, zero-extension, and essential coverage.

bind MULT MULT_sva #(.WIDTH(WIDTH)) i_MULT_sva();
module MULT_sva #(parameter WIDTH=32) ();
  default clocking cb @(posedge Valid_mult[0]); endclocking
  bit past_vld; initial past_vld = 1'b0; always @(cb) past_vld <= 1'b1;

  // No X at active edge
  assert property (cb !$isunknown({Amult,Bmult,Valid_mult,sel_mul_32x32}));

  // Registered inputs capture previous edge values
  assert property (cb past_vld |=> (Amult_reg == $past(Amult) &&
                                    Bmult_reg == $past(Bmult) &&
                                    Valid_mult_reg == $past(Valid_mult)));

  // Result update on same edge after NBA (##0); 1-cycle latency via regs
  assert property (cb past_vld && sel_mul_32x32 |-> ##0
                   (Cmult == ($past(Amult_reg) * $past(Bmult_reg))));
  assert property (cb past_vld && !sel_mul_32x32 |-> ##0
                   (Cmult == {2*WIDTH{1'b0}}));

  // Output only changes on valid edges (no glitches between edges)
  // If your tool supports throughout on clock gaps:
  assert property (cb $stable(Cmult));

  // Coverage: non-trivial multiply, zero operand, sel=0 path
  cover property (cb sel_mul_32x32 && (Amult!=0) && (Bmult!=0));
  cover property (cb sel_mul_32x32 && ((Amult==0) || (Bmult==0)));
  cover property (cb !sel_mul_32x32);
endmodule

bind mult_16x16 mult_16x16_sva i_mult_16x16_sva();
module mult_16x16_sva ();
  default clocking cb @(posedge Valid_mult[0]); endclocking
  bit past_vld; initial past_vld = 1'b0; always @(cb) past_vld <= 1'b1;

  // No X at active edge (top-level inputs)
  assert property (cb !$isunknown({Amult,Bmult,Valid_mult}));

  // Zero-extension correctness into 32-bit internal operands
  assert property (cb Amult_int == {16'h0000, Amult});
  assert property (cb Bmult_int == {16'h0000, Bmult});

  // Instance constant select tied high
  assert property (mult_inst.sel_mul_32x32 === 1'b1);

  // Functional correctness (1-cycle latency): low 32b equals 16x16 product
  assert property (cb past_vld |-> ##0 (Cmult == ($past(Amult) * $past(Bmult))));

  // Since inputs are zero-extended 16b, high 32b of 64b product must be zero
  assert property (cb past_vld |-> ##0 (Cmult_int[63:32] == 32'h0));

  // Coverage: interesting operand cases
  cover property (cb Amult==16'h0000 || Bmult==16'h0000);
  cover property (cb Amult==16'hFFFF && Bmult==16'hFFFF);
  cover property (cb Amult==16'h8000 && Bmult==16'h8000);
endmodule