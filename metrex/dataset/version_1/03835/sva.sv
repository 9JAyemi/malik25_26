// SVA bind file for nor_gate, mux_2to1, subtractor, top_module

// nor_gate assertions
module nor_gate_sva;
  default clocking cb @(*); endclocking

  // Functional check
  assert property (out === ~(a | b));

  // X-propagation: known inputs => known output
  assert property ((!$isunknown({a,b})) |-> (!$isunknown(out)));

  // Coverage: all input combinations
  cover property ({a,b} == 2'b00 && out==1'b1);
  cover property ({a,b} == 2'b01 && out==1'b0);
  cover property ({a,b} == 2'b10 && out==1'b0);
  cover property ({a,b} == 2'b11 && out==1'b0);
endmodule

bind nor_gate nor_gate_sva nor_gate_sva_i();

// mux_2to1 assertions
module mux_2to1_sva;
  default clocking cb @(*); endclocking

  // Structural NOR checks
  assert property (nor_a === ~(a | sel));
  assert property (nor_b === ~(b | ~sel));
  assert property (out   === ~(nor_a | nor_b));

  // Functional mux check
  assert property (out === (sel ? b : a));

  // X-propagation: known inputs => known outputs
  assert property ((!$isunknown({a,b,sel})) |-> (!$isunknown({out,nor_a,nor_b})));

  // Coverage: all select/data combinations
  cover property ({a,b,sel} == 3'b000);
  cover property ({a,b,sel} == 3'b001);
  cover property ({a,b,sel} == 3'b010);
  cover property ({a,b,sel} == 3'b011);
  cover property ({a,b,sel} == 3'b100);
  cover property ({a,b,sel} == 3'b101);
  cover property ({a,b,sel} == 3'b110);
  cover property ({a,b,sel} == 3'b111);

  // Coverage: each select branch observed with correct pass-through
  cover property (sel==0 && out===a);
  cover property (sel==1 && out===b);
endmodule

bind mux_2to1 mux_2to1_sva mux_2to1_sva_i();

// subtractor assertions
module subtractor_sva;
  default clocking cb @(*); endclocking

  // Constant check
  assert property (sub_const === 2'b01);

  // Functional check
  assert property (diff === (in - 2'b01));

  // X-propagation: known inputs => known outputs
  assert property ((!$isunknown(in)) |-> (!$isunknown(diff)));

  // Coverage: all input values and expected diffs
  cover property (in==2'b00 && diff==2'b11);
  cover property (in==2'b01 && diff==2'b00);
  cover property (in==2'b10 && diff==2'b01);
  cover property (in==2'b11 && diff==2'b10);
endmodule

bind subtractor subtractor_sva subtractor_sva_i();

// top_module assertions
module top_module_sva;
  default clocking cb @(*); endclocking

  // Mux function at top level
  assert property (mux_out === (sel ? b : a));

  // Connectivity into subtractor
  assert property (sub.in === {1'b0, mux_out});

  // Final function: subtract 1 from {0, mux_out}
  assert property (diff === ({1'b0, mux_out} - 2'b01));

  // Equivalent bit-level check
  assert property (diff === {~mux_out, ~mux_out});

  // X-propagation: known inputs => known outputs
  assert property ((!$isunknown({a,b,sel})) |-> (!$isunknown({mux_out,diff})));

  // Coverage: both mux decisions and resulting diffs
  cover property (sel==0 && mux_out===a);
  cover property (sel==1 && mux_out===b);
  cover property (mux_out==1'b0 && diff==2'b11);
  cover property (mux_out==1'b1 && diff==2'b00);
endmodule

bind top_module top_module_sva top_module_sva_i();