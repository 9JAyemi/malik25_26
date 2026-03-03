// SVA checker for xor_reset. Bind into the DUT.
// Focus: reset dominance, functional equivalence, X-propagation control, and concise coverage.
module xor_reset_sva (
  input in1,
  input in2,
  input reset,
  input out1
);

  // Sample on any relevant edge; check after ##0 to observe post-NBA combinational update
  // Functionality: reset dominates; otherwise out1 == in1 ^ in2
  property p_func;
    @(posedge in1 or negedge in1 or
      posedge in2 or negedge in2 or
      posedge reset or negedge reset or
      posedge out1 or negedge out1)
      1'b1 |-> ##0 (reset ? (out1 == 1'b0) : (out1 == (in1 ^ in2)));
  endproperty
  assert property (p_func)
    else $error("xor_reset functional mismatch: reset=%0b in1=%0b in2=%0b out1=%0b",
                reset, in1, in2, out1);

  // Out must be known when reset=1 or when reset=0 and inputs are known
  property p_known_out_when_known_in;
    @(posedge in1 or negedge in1 or
      posedge in2 or negedge in2 or
      posedge reset or negedge reset or
      posedge out1 or negedge out1)
      ((reset) || (!reset && !$isunknown({in1,in2}))) |-> ##0 (!$isunknown(out1));
  endproperty
  assert property (p_known_out_when_known_in)
    else $error("xor_reset produced X/Z on out1 with known driving condition");

  // Minimal, meaningful coverage: reset path and full XOR truth table under reset=0
  cover property (@(posedge in1 or negedge in1 or posedge in2 or negedge in2 or posedge reset or negedge reset or posedge out1 or negedge out1)
                  ##0 (reset && out1==1'b0));

  cover property (@(posedge in1 or negedge in1 or posedge in2 or negedge in2 or posedge reset or negedge reset or posedge out1 or negedge out1)
                  ##0 (!reset && in1==1'b0 && in2==1'b0 && out1==1'b0));
  cover property (@(posedge in1 or negedge in1 or posedge in2 or negedge in2 or posedge reset or negedge reset or posedge out1 or negedge out1)
                  ##0 (!reset && in1==1'b0 && in2==1'b1 && out1==1'b1));
  cover property (@(posedge in1 or negedge in1 or posedge in2 or negedge in2 or posedge reset or negedge reset or posedge out1 or negedge out1)
                  ##0 (!reset && in1==1'b1 && in2==1'b0 && out1==1'b1));
  cover property (@(posedge in1 or negedge in1 or posedge in2 or negedge in2 or posedge reset or negedge reset or posedge out1 or negedge out1)
                  ##0 (!reset && in1==1'b1 && in2==1'b1 && out1==1'b0));

  // Optional concise toggle coverage: input toggle causes output update when reset=0
  cover property (@(posedge in1 or negedge in1) !reset ##0 $changed(out1));
  cover property (@(posedge in2 or negedge in2) !reset ##0 $changed(out1));

endmodule

// Bind into DUT (tool/scope permitting)
bind xor_reset xor_reset_sva xor_reset_sva_i (.*);