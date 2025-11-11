// SVA for mux_4to1
module mux_4to1_sva (
  input logic A, B, C, D,
  input logic S0, S1,
  input logic Y
);

  default clocking cb @($global_clock); endclocking

  // Pure combinational decode of the selected input (propagates X/Z)
  function automatic logic sel_val (logic s1, s0, a, b, c, d);
    unique case ({s1,s0})
      2'b00: sel_val = a;
      2'b01: sel_val = b;
      2'b10: sel_val = c;
      2'b11: sel_val = d;
      default: sel_val = 1'bx;
    endcase
  endfunction

  // Functional correctness when selects are known
  property p_func;
    !$isunknown({S1,S0}) |-> (Y === sel_val(S1,S0,A,B,C,D));
  endproperty
  assert property (p_func);

  // Output must be known when selects and selected input are known
  property p_no_x_when_inputs_known;
    (!$isunknown({S1,S0}) && !$isunknown(sel_val(S1,S0,A,B,C,D))) |-> !$isunknown(Y);
  endproperty
  assert property (p_no_x_when_inputs_known);

  // Purely combinational: No spurious output change if nothing driving it changed
  property p_no_spurious_glitch;
    !$changed({A,B,C,D,S0,S1}) |-> $stable(Y);
  endproperty
  assert property (p_no_spurious_glitch);

  // Zero-delay response: any driving change updates Y in the same time slot
  property p_zero_delay_response;
    $changed({A,B,C,D,S0,S1}) |-> ##0 (Y === sel_val(S1,S0,A,B,C,D));
  endproperty
  assert property (p_zero_delay_response);

  // Minimal functional coverage
  cover property (!$isunknown({S1,S0}) && {S1,S0}==2'b00 && (Y === A));
  cover property (!$isunknown({S1,S0}) && {S1,S0}==2'b01 && (Y === B));
  cover property (!$isunknown({S1,S0}) && {S1,S0}==2'b10 && (Y === C));
  cover property (!$isunknown({S1,S0}) && {S1,S0}==2'b11 && (Y === D));

  // Cover select changes cause recomputation in same delta
  cover property ($changed({S1,S0}) ##0 (Y === sel_val(S1,S0,A,B,C,D)));

  // Optional: observe unknown select scenario
  cover property ($isunknown({S1,S0}));

endmodule

// Bind into the DUT
bind mux_4to1 mux_4to1_sva mux_4to1_sva_i (
  .A(A), .B(B), .C(C), .D(D),
  .S0(S0), .S1(S1),
  .Y(Y)
);