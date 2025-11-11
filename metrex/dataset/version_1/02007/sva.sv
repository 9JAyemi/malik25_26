// SVA checker for TOP AND gate
module TOP_sva(input logic in0, in1, out);

  // Functional correctness at all times (4-state check)
  always_comb assert (out === (in0 & in1))
    else $error("TOP AND: out != (in0 & in1)");

  // Zero-delay update on any input change
  property p_zero_delay_update;
    @(posedge in0 or negedge in0 or posedge in1 or negedge in1)
      1 |-> ##0 (out === (in0 & in1));
  endproperty
  assert property (p_zero_delay_update)
    else $error("TOP AND: out not updated same cycle on input change");

  // No spurious out changes
  property p_no_spurious_out_change;
    @(posedge out or negedge out) $changed(in0) || $changed(in1);
  endproperty
  assert property (p_no_spurious_out_change)
    else $error("TOP AND: out changed without input change");

  // Out must be known when inputs are known
  property p_known_out_when_inputs_known;
    @(posedge in0 or negedge in0 or posedge in1 or negedge in1 or posedge out or negedge out)
      !$isunknown({in0,in1}) |-> !$isunknown(out);
  endproperty
  assert property (p_known_out_when_inputs_known)
    else $error("TOP AND: out X/Z while inputs are known");

  // Functional coverage: all input/output combinations
  cover property (@(posedge in0 or negedge in0 or posedge in1 or negedge in1) (!in0 && !in1 && out==0));
  cover property (@(posedge in0 or negedge in0 or posedge in1 or negedge in1) (!in0 &&  in1 && out==0));
  cover property (@(posedge in0 or negedge in0 or posedge in1 or negedge in1) ( in0 && !in1 && out==0));
  cover property (@(posedge in0 or negedge in0 or posedge in1 or negedge in1) ( in0 &&  in1 && out==1));

endmodule

// Bind the checker to the DUT
bind TOP TOP_sva sva_TOP_inst(.in0(in0), .in1(in1), .out(out));