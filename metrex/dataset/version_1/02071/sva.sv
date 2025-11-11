// SVA for amiq_mux2_1
// Bind into DUT for checking and coverage

module amiq_mux2_1_sva(input clk, input sel, input in0, input in1, input out);

  default clocking cb @(posedge clk); endclocking

  // First sampled clock tick detector
  let first_tick = !$past(1'b1, 1, 0);

  // Basic sanity: no X on inputs/outputs at sampling
  a_no_x_inputs: assert property (!$isunknown({sel,in0,in1}));
  a_no_x_out   : assert property (!$isunknown(out));

  // Initial condition from DUT's "initial out=0;"
  a_init_out_zero: assert property (first_tick |-> out == 1'b0);

  // Functional correctness: 1-cycle registered 2:1 mux
  a_mux_func: assert property (disable iff (first_tick)
                               out == $past(sel ? in1 : in0));

  // Optional: out should not glitch between clocks (registered design)
  a_no_glitch_midcycle: assert property (@(negedge clk) $stable(out));

  // Coverage: exercise both data paths and sel transitions
  c_path0: cover property (sel==1'b0 ##1 out == $past(in0));
  c_path1: cover property (sel==1'b1 ##1 out == $past(in1));
  c_sel_0_to_1: cover property (sel==1'b0 ##1 sel==1'b1);
  c_sel_1_to_0: cover property (sel==1'b1 ##1 sel==1'b0);

  // Coverage: data-driven toggles propagate when selected
  c_in0_toggle: cover property (sel==1'b0 && (in0 != $past(in0)) ##1 out != $past(out));
  c_in1_toggle: cover property (sel==1'b1 && (in1 != $past(in1)) ##1 out != $past(out));

endmodule

bind amiq_mux2_1 amiq_mux2_1_sva i_amiq_mux2_1_sva(.clk(clk), .sel(sel), .in0(in0), .in1(in1), .out(out));