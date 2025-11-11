// SVA checker for xor_inverter. Bind this to the DUT.
module xor_inverter_sva #(parameter W=8) (
  input logic [W-1:0] a,
  input logic [W-1:0] b,
  input logic         ctrl,
  input logic [W-1:0] out
);

  // Create a combinational sampling event
  event comb_ev;
  always @(a or b or ctrl or out) -> comb_ev;

  // Functional correctness when inputs are known
  property p_func;
    !$isunknown({a,b,ctrl}) |-> (out == (ctrl ? ~(a ^ b) : (a ^ b)));
  endproperty
  a_func: assert property (@(comb_ev) p_func)
    else $error("xor_inverter mismatch: ctrl=%0b a=%0h b=%0h out=%0h exp=%0h",
                ctrl, a, b, out, (ctrl ? ~(a ^ b) : (a ^ b)));

  // Out must not be X/Z when inputs are known
  a_no_x: assert property (@(comb_ev)
                           (!$isunknown({a,b,ctrl})) |-> !$isunknown(out))
    else $error("xor_inverter: out has X/Z with known inputs");

  // Output must invert if only ctrl toggles (a,b stable)
  property p_ctrl_flip;
    $changed(ctrl) && $stable({a,b}) &&
    !$isunknown({a,b,ctrl,$past(ctrl)}) |-> (out == ~ $past(out));
  endproperty
  a_ctrl_flip: assert property (@(comb_ev) p_ctrl_flip)
    else $error("xor_inverter: out did not invert on ctrl toggle with stable a,b");

  // No spurious output changes when inputs and ctrl are stable
  property p_no_spurious_glitch;
    $stable({a,b,ctrl}) && !$isunknown({a,b,ctrl}) |-> $stable(out);
  endproperty
  a_no_glitch: assert property (@(comb_ev) p_no_spurious_glitch)
    else $error("xor_inverter: out changed without input/ctrl change");

  // Coverage: both modes and key patterns
  c_mode_xor :  cover property (@(comb_ev)
                   (!$isunknown({a,b,ctrl})) && (ctrl==0) &&
                   (out == (a ^ b)));
  c_mode_xnor:  cover property (@(comb_ev)
                   (!$isunknown({a,b,ctrl})) && (ctrl==1) &&
                   (out == ~(a ^ b)));
  c_a_eq_b   :  cover property (@(comb_ev)
                   (!$isunknown({a,b,ctrl})) && (a==b) &&
                   (out == (ctrl ? ~'0 : '0)));
  c_a_eq_n_b:  cover property (@(comb_ev)
                   (!$isunknown({a,b,ctrl})) && (a==~b) &&
                   (out == (ctrl ? '0 : ~'0)));
  c_ctrl_toggle: cover property (@(comb_ev) $changed(ctrl) && $stable({a,b}));

endmodule

// Bind to the DUT
bind xor_inverter xor_inverter_sva #(.W(8)) xor_inverter_sva_i (
  .a(a), .b(b), .ctrl(ctrl), .out(out)
);