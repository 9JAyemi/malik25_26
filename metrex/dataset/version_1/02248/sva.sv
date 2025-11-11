// SVA for top_module and submodules (bindable, concise, full functional checks and key coverage)

bind top_module          top_module_sva          top_module_sva_i();
bind unsigned_multiplier unsigned_multiplier_sva unsigned_multiplier_sva_i();
bind add_sub             add_sub_sva             add_sub_sva_i();
bind functional_module   functional_module_sva   functional_module_sva_i();

module top_module_sva;
  // Clock on any top-level input change
  default clocking cb @(multiplier or multiplicand or ctrl or in0 or in1); endclocking

  // Helpers
  let known_inputs     = !$isunknown({multiplier, multiplicand, ctrl, in0, in1});
  let addsub_exp       = (ctrl ? (multiplier - multiplicand) : (multiplier + multiplicand)) & 4'hF;
  let final_exp        = {8'h00, (multiplier * multiplicand)} + {12'h000, addsub_exp};
  let out_exp          = ctrl ? ({1'b0,final_out}+{1'b0,in0}+{1'b0,in1})[15:0] : final_out;
  let add3_carry       = ({1'b0,final_out}+{1'b0,in0}+{1'b0,in1})[16];

  // Functional correctness across hierarchy
  a_mul_top:     assert property (known_inputs |-> unsigned_mult_out == multiplier * multiplicand);
  a_addsub_top:  assert property (known_inputs |-> add_sub_out      == addsub_exp);
  a_final_top:   assert property (known_inputs |-> final_out         == final_exp);
  a_out_top:     assert property (known_inputs |-> out               == out_exp);

  // X-propagation guard
  a_known_outs:  assert property (known_inputs |-> !$isunknown({unsigned_mult_out, add_sub_out, final_out, out}));

  // Key coverage
  c_ctrl0:       cover  property (known_inputs && !ctrl);
  c_ctrl1:       cover  property (known_inputs &&  ctrl);
  c_add3_ovf:    cover  property (known_inputs &&  ctrl && add3_carry);
endmodule

module unsigned_multiplier_sva;
  default clocking cb @(a or b); endclocking
  let known = !$isunknown({a,b});

  a_mul:   assert property (known |-> p == a * b);
  a_known: assert property (known |-> !$isunknown(p));

  // Coverage: zero, max, mixed
  c_zero:  cover  property (known && (a==0 || b==0) && p==0);
  c_max:   cover  property (known && a==4'hF && b==4'hF && p==8'hE1);
endmodule

module add_sub_sva;
  default clocking cb @(a or b or ctrl); endclocking
  let known = !$isunknown({a,b,ctrl});
  let exp_s = ((ctrl ? (a - b) : (a + b)) & 4'hF);

  a_addsub:   assert property (known |-> s == exp_s);
  a_known:    assert property (known |-> !$isunknown(s));

  // Coverage: add overflow and sub underflow
  c_add:      cover  property (known && !ctrl);
  c_add_ovf:  cover  property (known && !ctrl && ({1'b0,a}+{1'b0,b})[4]);
  c_sub:      cover  property (known &&  ctrl);
  c_sub_udf:  cover  property (known &&  ctrl && (a < b));
endmodule

module functional_module_sva;
  default clocking cb @(in0 or in1); endclocking
  let known = !$isunknown({in0,in1});
  let exp_o = {8'h00, in0} + {12'h000, in1};

  a_func:   assert property (known |-> out == exp_o);
  a_known:  assert property (known |-> !$isunknown(out));

  // Coverage: extremes
  c_zero:   cover  property (known && in0==8'h00 && in1==4'h0 && out==16'h0000);
  c_max:    cover  property (known && in0==8'hFF && in1==4'hF);
endmodule