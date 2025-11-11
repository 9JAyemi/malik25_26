// SVA for sub_mult_32bit
// Bind into the DUT to access internal signals like B_inv.
module sub_mult_32bit_sva (sub_mult_32bit dut);

  // No X/Z on outputs when inputs are known
  property p_no_x;
    @(dut.A or dut.B)
      (!$isunknown({dut.A,dut.B})) |-> ##0 !$isunknown({dut.D,dut.P});
  endproperty
  assert property (p_no_x);

  // Subtraction correctness: D = A + (~B) + 1  (mod 2^32)
  property p_sub_eq;
    @(dut.A or dut.B)
      (!$isunknown({dut.A,dut.B})) |-> ##0
        dut.D == (dut.A + (~dut.B) + 32'd1);
  endproperty
  assert property (p_sub_eq);

  // Subtraction modulo consistency: (D + B) mod 2^32 = A
  property p_sub_mod;
    @(dut.A or dut.B or dut.D)
      (!$isunknown({dut.A,dut.B})) |-> ##0
        ((dut.D + dut.B) == dut.A);
  endproperty
  assert property (p_sub_mod);

  // Multiplication correctness (unsigned): P = A * B
  property p_mul_eq;
    @(dut.A or dut.B)
      (!$isunknown({dut.A,dut.B})) |-> ##0
        dut.P == ($unsigned(dut.A) * $unsigned(dut.B));
  endproperty
  assert property (p_mul_eq);

  // Internal mirror check: B_inv always equals bitwise ~B
  property p_b_inv;
    @(dut.B)
      (!$isunknown(dut.B)) |-> ##0 (dut.B_inv == ~dut.B);
  endproperty
  assert property (p_b_inv);

  // Combinational sanity: outputs change only when inputs change
  property p_out_change_implies_in_change;
    @(dut.A or dut.B or dut.D or dut.P)
      disable iff ($isunknown({dut.A,dut.B,dut.D,dut.P}))
      1 |-> ##0
        (($changed(dut.D) || $changed(dut.P)) -> ($changed(dut.A) || $changed(dut.B)));
  endproperty
  assert property (p_out_change_implies_in_change);

  // Coverage: key corner cases
  cover property (@(dut.A or dut.B)
    (!$isunknown({dut.A,dut.B})) ##0
      (dut.A==32'd0 && dut.B==32'd0 && dut.D==32'd0 && dut.P==64'd0));

  cover property (@(dut.A or dut.B)
    (!$isunknown({dut.A,dut.B})) |-> ##0 (dut.B==32'd0 && dut.P==64'd0));

  cover property (@(dut.A or dut.B)
    (!$isunknown({dut.A,dut.B})) |-> ##0 (dut.A==32'd0 && dut.P==64'd0));

  cover property (@(dut.A or dut.B)
    (!$isunknown({dut.A,dut.B})) |-> ##0 (dut.B==32'd1 && dut.P==$unsigned(dut.A)));

  cover property (@(dut.A or dut.B)
    (!$isunknown({dut.A,dut.B})) |-> ##0 $onehot(dut.B));

  cover property (@(dut.A or dut.B)
    (!$isunknown({dut.A,dut.B})) |-> ##0 (dut.A<dut.B && dut.D>dut.A));

  cover property (@(dut.A or dut.B)
    (!$isunknown({dut.A,dut.B})) |-> ##0
      (dut.A==32'hFFFF_FFFF && dut.B==32'hFFFF_FFFF));

endmodule

// Bind into all instances of sub_mult_32bit
bind sub_mult_32bit sub_mult_32bit_sva sva_inst();