// SVA for top_module and submodules. Bind these to the DUT.
// Focused, high-quality checks and key coverage.

bind top_module top_module_sva u_top_module_sva();
module top_module_sva;
  // Access top_module scope: clk, reset, in, transition_detected, equal_a_b
  default clocking cb @ (posedge clk); endclocking

  // Comparator correctness at integration point
  a_equal_correct: assert property ( equal_a_b == (in[31:28] == in[27:24]) );

  // Transition detector behavior (1-cycle pulse on any MSB change)
  a_td_equiv:     assert property ( transition_detected == (in[31] ^ $past(in[31],1,reset)) );

  // Key coverage
  c_td_rise:  cover property ( $rose(in[31]) && transition_detected );
  c_td_fall:  cover property ( $fell(in[31]) && transition_detected );
  c_eq_true:  cover property ( equal_a_b );
  c_eq_false: cover property ( !equal_a_b );
endmodule


bind functional_module fm_sva u_fm_sva();
module fm_sva;
  // Access functional_module scope: clk, reset, in, equal, out, pattern, pattern_index
  default clocking cb @ (posedge clk); endclocking

  // Synchronous reset sets index to 0
  a_idx_reset: assert property ( reset |=> pattern_index == 32'd0 );

  // Next-state relation (handles increment and wrap; NBA ordering respected)
  a_idx_next: assert property (
    pattern_index == ( ($past(pattern_index,1,reset) == 32'd31) ? 32'd0 :
                       ($past(equal,1,reset) ? $past(pattern_index,1,reset) + 32'd1
                                              : $past(pattern_index,1,reset) ) )
  );

  // Index stays in range [0:31]
  a_idx_range: assert property ( pattern_index inside {[32'd0:32'd31]} );

  // Output must match selected pattern bit
  a_out_map:   assert property ( out == pattern[pattern_index] );

  // Pattern is constant
  a_pat_const: assert property ( $stable(pattern) );

  // Coverage: increment, wrap, and both out values
  c_inc:  cover property ( $past(equal,1,reset) && pattern_index == $past(pattern_index,1,reset) + 32'd1 );
  c_wrap: cover property ( $past(pattern_index,1,reset) == 32'd31 && pattern_index == 32'd0 );
  c_out1: cover property ( out == 1'b1 );
  c_out0: cover property ( out == 1'b0 );
endmodule


bind transition_detector td_sva u_td_sva();
module td_sva;
  // Access transition_detector scope: clk, reset, in, prev_in, transition_detected
  default clocking cb @ (posedge clk); endclocking

  // prev_in samples in every cycle (except reset)
  a_prev_sample: assert property ( prev_in == $past(in,1,reset) );

  // transition_detected is already checked at top; keep internals concise.
endmodule