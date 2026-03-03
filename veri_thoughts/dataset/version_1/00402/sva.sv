// SVA for arithmetic_circuit
// Bind-in module; accesses DUT signals directly
module arithmetic_circuit_sva;

  // past_valid guard for $past()
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clock) past_valid <= 1'b1;

  // Functional correctness (nonblocking flop semantics)
  assert property (@(posedge clock) disable iff (!past_valid)
                   temp == $past(c_in - d_in));

  assert property (@(posedge clock) disable iff (!past_valid)
                   out1 == $past(temp - d_in));

  // X-propagation safety (given known sources)
  assert property (@(posedge clock) disable iff (!past_valid)
                   !$isunknown({$past(c_in), $past(d_in)}) |-> !$isunknown(temp));

  assert property (@(posedge clock) disable iff (!past_valid)
                   !$isunknown({$past(temp), $past(d_in)}) |-> !$isunknown(out1));

  // No glitches between rising edges
  assert property (@(negedge clock) $stable(temp) && $stable(out1));

  // Coverage: exercise all input combinations
  cover property (@(posedge clock) c_in==0 && d_in==0);
  cover property (@(posedge clock) c_in==0 && d_in==1);
  cover property (@(posedge clock) c_in==1 && d_in==0);
  cover property (@(posedge clock) c_in==1 && d_in==1);

  // Coverage: observe both flop updates and out1 activity
  cover property (@(posedge clock) disable iff (!past_valid)
                  temp == $past(c_in - d_in));
  cover property (@(posedge clock) disable iff (!past_valid)
                  out1 == $past(temp - d_in));
  cover property (@(posedge clock) $rose(out1));
  cover property (@(posedge clock) $fell(out1));

endmodule

bind arithmetic_circuit arithmetic_circuit_sva;