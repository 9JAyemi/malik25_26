// SVA binder for trig_functions
module trig_functions_sva (trig_functions dut);

  // Use input x edges as a sample event for this purely combinational DUT
  default clocking cb @(posedge dut.x or negedge dut.x); endclocking

  // Sanity: inputs/outputs known
  a_known: assert property (@cb !$isunknown({dut.x, dut.sin_out, dut.cos_out, dut.tan_out}))
    else $error("X/Z detected on I/O");

  // Special-case: x==0 forces exact outputs
  a_x0: assert property (@cb (dut.x==1'b0) |-> ##0 (dut.sin_out==1'b0 && dut.cos_out==1'b1 && dut.tan_out==1'b0))
    else $error("x==0 behavior wrong");

  // Priority: when x==0, cos_out must be 1 (so tan_out is 0, not 1)
  a_x0_cos1: assert property (@cb (dut.x==1'b0) |-> ##0 (dut.cos_out==1'b1))
    else $error("x==0 did not force cos_out==1");

  // cos_out==0 forces tan_out==1 (final if-statement behavior)
  a_cos0_tan1: assert property (@cb (dut.cos_out==1'b0) |-> ##0 (dut.tan_out==1'b1))
    else $error("cos_out==0 did not force tan_out==1");

  // Otherwise tan_out equals sin_out/cos_out -> with 1b cos_out==1, tan_out==sin_out
  a_cos1_tan_eq_sin: assert property (@cb (dut.cos_out==1'b1) |-> ##0 (dut.tan_out==dut.sin_out))
    else $error("tan_out != sin_out when cos_out==1");

  // Outputs must only change as a result of x changing (pure combinational fanin)
  a_out_change_caused_by_x: assert property (
    @(posedge dut.sin_out or negedge dut.sin_out or
      posedge dut.cos_out or negedge dut.cos_out or
      posedge dut.tan_out or negedge dut.tan_out) $changed(dut.x))
    else $error("Output changed without x changing");

  // Internal invariants from the fixed for-loop
  a_sign_final: assert property (@cb dut.sign == 32'hFFFF_FFFF)
    else $error("Final sign not -1");
  a_i_final: assert property (@cb dut.i == 32'd17)
    else $error("Final loop index i not 17");

  // Coverage
  c_x0:     cover property (@cb dut.x==1'b0 && dut.sin_out==1'b0 && dut.cos_out==1'b1 && dut.tan_out==1'b0);
  c_x1:     cover property (@cb dut.x==1'b1);
  c_cos0:   cover property (@cb dut.cos_out==1'b0 && dut.tan_out==1'b1);
  c_cos1:   cover property (@cb dut.cos_out==1'b1 && dut.tan_out==dut.sin_out);
  c_tan0:   cover property (@cb dut.tan_out==1'b0);
  c_tan1:   cover property (@cb dut.tan_out==1'b1);

endmodule

// Bind into DUT
bind trig_functions trig_functions_sva sva_inst(.dut);