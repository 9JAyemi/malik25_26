// SVA for phase_detector
module phase_detector_sva (
  input clk,
  input ref,
  input in,
  input error,
  input ref_reg,
  input in_reg
);
  default clocking cb @(posedge clk); endclocking

  // Registers capture inputs (1-cycle latency), when past is known
  a_cap_ref: assert property ( !$isunknown($past(ref)) |-> (ref_reg == $past(ref)) );
  a_cap_in : assert property ( !$isunknown($past(in))  |-> (in_reg  == $past(in))  );

  // Functional spec: error = XOR of prior-cycle inputs (when known)
  a_func_past_in: assert property ( !$isunknown($past({ref,in})) |-> (error == ($past(ref) ^ $past(in))) );

  // Structural check: error = XOR of current regs (when known)
  a_struct_regs: assert property ( !$isunknown({ref_reg,in_reg}) |-> (error == (ref_reg ^ in_reg)) );

  // No X on error once prior inputs are known
  a_no_x_error: assert property ( !$isunknown($past({ref,in})) |-> !$isunknown(error) );

  // Coverage: both XOR outcomes observed
  c_err1: cover property ( !$isunknown($past({ref,in})) && ($past(ref) ^ $past(in)) && (error == 1) );
  c_err0: cover property ( !$isunknown($past({ref,in})) && !($past(ref) ^ $past(in)) && (error == 0) );

  // Coverage: error toggles
  c_rise: cover property ( $rose(error) );
  c_fall: cover property ( $fell(error) );
endmodule

// Bind into the DUT (ports match DUT internal names via .*)
bind phase_detector phase_detector_sva sva_i (.*);