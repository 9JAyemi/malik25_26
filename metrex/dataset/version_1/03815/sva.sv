// SVA for nor_gate_with_enable
// Bind into DUT; concise, full functional checking and coverage.

module nor_gate_with_enable_sva (
  input in1,
  input in2,
  input en,
  input out
);

  // Helper: inputs known
  function automatic bit valid_i;
    valid_i = !$isunknown({in1,in2,en});
  endfunction

  // Inputs must be known (flag X/Z on control/data)
  assert property (@(in1 or in2 or en) !$isunknown({in1,in2,en}))
    else $error("nor_gate_with_enable: X/Z on inputs");

  // Output must be known whenever inputs are known
  assert property (@(in1 or in2 or en or out) valid_i |-> !$isunknown(out))
    else $error("nor_gate_with_enable: X/Z on out with known inputs");

  // Functional correctness (combinational, settle in same timestep)
  assert property (@(in1 or in2 or en) valid_i |-> ##0
                   out == (en ? ~(in1 | in2) : 1'b0))
    else $error("nor_gate_with_enable: functional mismatch");

  // Strong enables: explicit cases (helpful, precise debug)
  assert property (@(en) valid_i && !en |-> ##0 out == 1'b0)
    else $error("nor_gate_with_enable: en=0 but out!=0");

  assert property (@(in1 or in2 or en) valid_i && en |-> ##0
                   out == (~(in1 | in2)))
    else $error("nor_gate_with_enable: en=1 but out!=~(in1|in2)");

  // No spurious output toggles without input/en change
  assert property (@(in1 or in2 or en or out)
                   $changed(out) |-> ($changed(in1) || $changed(in2) || $changed(en)))
    else $error("nor_gate_with_enable: out changed without cause");

  // Coverage: truth table when enabled
  cover property (@(in1 or in2 or en) en && {in1,in2}==2'b00 ##0 out==1'b1);
  cover property (@(in1 or in2 or en) en && {in1,in2}==2'b01 ##0 out==1'b0);
  cover property (@(in1 or in2 or en) en && {in1,in2}==2'b10 ##0 out==1'b0);
  cover property (@(in1 or in2 or en) en && {in1,in2}==2'b11 ##0 out==1'b0);

  // Coverage: disabled case forces 0 (any inputs)
  cover property (@(in1 or in2 or en) !en ##0 out==1'b0);

  // Coverage: enable edge behaviors
  cover property (@(en) $rose(en) && (in1==0 && in2==0) ##0 out==1'b1);
  cover property (@(en) $rose(en) && (in1 || in2) ##0 out==1'b0);
  cover property (@(en) $fell(en) ##0 out==1'b0);

endmodule

// Bind into the DUT
bind nor_gate_with_enable nor_gate_with_enable_sva i_nor_gate_with_enable_sva (
  .in1(in1),
  .in2(in2),
  .en(en),
  .out(out)
);