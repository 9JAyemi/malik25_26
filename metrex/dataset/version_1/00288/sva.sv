// SVA for var6_multi: concise, high-signal-quality checks and coverage
// Bind-in so no DUT edits required

module var6_multi_sva;

  // Knownness: when inputs are 0/1, outputs must be known
  ap_known: assert property (@(*)
    (!$isunknown({A,B,C,D,E,F})) |-> (!$isunknown(valid) && !$isunknown(total_value[1]) && (total_value[0]===1'b0))
  );

  // total_value mapping
  ap_tv1: assert property (@(*) total_value[1] === E);
  ap_tv0: assert property (@(*) total_value[0] === 1'b0);

  // Ternary selects behave correctly
  ap_25_e1: assert property (@(*) E  |-> (_25 === _43));
  ap_25_e0: assert property (@(*) !E |-> (_25 === _01));
  ap_41_e1: assert property (@(*) E  |-> (_41 === C));
  ap_41_e0: assert property (@(*) !E |-> (_41 === ~B));

  // E-dependent XOR on _20
  ap_20_e1: assert property (@(*) E  |-> (_20 === _19));
  ap_20_e0: assert property (@(*) !E |-> (_20 === ~_19));

  // NOR implies NAND for same operands (_26_ => _03_)
  ap_nor_implies_nand: assert property (@(*) _26_ |-> _03_);

  // E-gating impact on _23/_24
  ap_24_e0: assert property (@(*) !E |-> (_23 === 1'b0 && _24 === _07));
  ap_24_e1: assert property (@(*) E  |-> (_23 === _03   && _24 === (_03 ^ _07)));

  // valid implications from its decomposition
  ap_v_block42:   assert property (@(*) _42_ |-> !valid);
  ap_v_block3829: assert property (@(*) (_38_ && _29_) |-> !valid);
  ap_v_pass:      assert property (@(*) (!_42_ && !_38_) |-> valid);

  // Or-composition sanity
  ap_29_hi: assert property (@(*) (_28_ || _21_) |-> _29_);
  ap_29_lo: assert property (@(*) !_29_ |-> (!_28_ && !_21_));

  // Combinational stability: if inputs stable, outputs stable
  ap_stable: assert property (@(*) $stable({A,B,C,D,E,F}) |-> $stable({valid,total_value[1:0]}));

  // Coverage: exercise key modes and outcomes
  cp_e0: cover property (@(*) !E);
  cp_e1: cover property (@(*) E);
  cp_f0: cover property (@(*) !F);
  cp_f1: cover property (@(*) F);
  cp_valid0: cover property (@(*) (valid==1'b0));
  cp_valid1: cover property (@(*) (valid==1'b1));
  cp_valid_rise: cover property (@(*) $rose(valid));
  cp_valid_fall: cover property (@(*) $fell(valid));
  cp_sel25_0: cover property (@(*) (!E && (_25===_01)));
  cp_sel25_1: cover property (@(*) ( E && (_25===_43)));
  cp_sel41_0: cover property (@(*) (!E && (_41===~B)));
  cp_sel41_1: cover property (@(*) ( E && (_41===C)));
  cp_v_by_42:   cover property (@(*) (_42_ && !valid));
  cp_v_by_3829: cover property (@(*) (_38_ && _29_ && !valid));
  cp_v_pass:    cover property (@(*) (!_42_ && !_38_ && valid));

endmodule

bind var6_multi var6_multi_sva sva_inst();