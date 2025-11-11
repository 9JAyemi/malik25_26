// SVA for PLL/phase_detector/loop_filter
// Bind these into the DUT; focuses on key functional checks and concise coverage

// ---------------- PLL ----------------
module pll_sva #(
  parameter int m      = 10,
  parameter int f_ref  = 100000,
  parameter int f_out  = 1000000
)(
  input  logic         ref_clk,
  input  logic         ctrl,
  input  logic         synth_clk,
  // internals
  input  logic [31:0]  phase_accumulator,
  input  logic [31:0]  feedback_clk_counter,
  input  logic         feedback_clk,
  input  logic         synth_clk_reg
);
  localparam int THRESH = (f_ref / m) - 1;
  localparam int KSTEP  = (f_out * m) / f_ref;

  // Feedback pulse is correct compare on counter
  assert property (@(posedge ref_clk) feedback_clk == (feedback_clk_counter == THRESH));

  // Counter operation and bounds
  assert property (@(posedge ref_clk) feedback_clk |-> feedback_clk_counter == 0);
  assert property (@(posedge ref_clk) !feedback_clk |-> feedback_clk_counter == $past(feedback_clk_counter)+1);
  assert property (@(posedge ref_clk) feedback_clk_counter <= THRESH);

  // Feedback pulse is single-cycle and periodic with exact gap
  assert property (@(posedge ref_clk) feedback_clk |=> !feedback_clk);
  assert property (@(posedge ref_clk) feedback_clk |=> (!feedback_clk[*THRESH]) ##1 feedback_clk);

  // Synth clock reg/accumulator behavior on negedge ref_clk
  assert property (@(negedge ref_clk)
                   ($past(phase_accumulator) < m)
                   |-> (phase_accumulator == $past(phase_accumulator) + KSTEP) && (synth_clk_reg != $past(synth_clk_reg)));
  assert property (@(negedge ref_clk)
                   !($past(phase_accumulator) < m)
                   |-> (phase_accumulator == 0) && (synth_clk_reg == $past(synth_clk_reg)));

  // Output matches internal reg
  assert property (@(posedge ref_clk or negedge ref_clk) synth_clk == synth_clk_reg);

  // Coverage
  cover property (@(posedge ref_clk) feedback_clk ##[1:THRESH] feedback_clk);
  cover property (@(negedge ref_clk) synth_clk_reg != $past(synth_clk_reg));
  cover property (@(negedge ref_clk) (phase_accumulator == 0) && ($past(phase_accumulator) >= m));
endmodule

bind PLL pll_sva #(.m(m), .f_ref(f_ref), .f_out(f_out)) pll_sva_i(
  .ref_clk(ref_clk),
  .ctrl(ctrl),
  .synth_clk(synth_clk),
  .phase_accumulator(phase_accumulator),
  .feedback_clk_counter(feedback_clk_counter),
  .feedback_clk(feedback_clk),
  .synth_clk_reg(synth_clk_reg)
);

// ---------------- phase_detector ----------------
module phase_detector_sva(
  input  logic ref_clk,
  input  logic feedback_clk,
  input  logic phase_difference,
  // internals
  input  logic ref_clk_last,
  input  logic feedback_clk_last
);
  // Sampling registers capture on their respective negedges
  assert property (@(negedge ref_clk)      ref_clk_last      == $past(ref_clk));
  assert property (@(negedge feedback_clk) feedback_clk_last == $past(feedback_clk));

  // Output equals XOR of sampled clocks
  assert property (@(posedge ref_clk or negedge ref_clk or posedge feedback_clk or negedge feedback_clk)
                   phase_difference == (ref_clk_last ^ feedback_clk_last));

  // Coverage on phase_difference activity
  cover property (@(posedge ref_clk or posedge feedback_clk) $rose(phase_difference));
  cover property (@(posedge ref_clk or posedge feedback_clk) $fell(phase_difference));
endmodule

bind phase_detector phase_detector_sva pd_sva_i(
  .ref_clk(ref_clk),
  .feedback_clk(feedback_clk),
  .phase_difference(phase_difference),
  .ref_clk_last(ref_clk_last),
  .feedback_clk_last(feedback_clk_last)
);

// ---------------- loop_filter ----------------
module loop_filter_sva #(
  parameter int kp = 1,
  parameter int ki = 1
)(
  input  logic        ctrl,
  input  logic        phase_difference,
  // internals/outputs
  input  logic [31:0] integrator,
  input  logic [31:0] loop_filter_output
);
  // Integrator updates only on negedge ctrl by +phase_difference
  assert property (@(negedge ctrl) integrator == $past(integrator) + $past(phase_difference));
  assert property (@(posedge ctrl) integrator == $past(integrator));

  // Output equals integrator*ki
  assert property (@(posedge ctrl or negedge ctrl) loop_filter_output == integrator * ki);

  // Coverage: observe increment and hold
  cover property (@(negedge ctrl) phase_difference && (integrator == $past(integrator)+1));
  cover property (@(negedge ctrl) !phase_difference && (integrator == $past(integrator)));
endmodule

bind loop_filter loop_filter_sva #(.kp(kp), .ki(ki)) lf_sva_i(
  .ctrl(ctrl),
  .phase_difference(phase_difference),
  .integrator(integrator),
  .loop_filter_output(loop_filter_output)
);