// SVA for adder/overflow chain. Bind to top_module.
// Focus: functional correctness, connectivity, X-propagation, and key corner-case coverage.

module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [7:0]  a,
  input  logic [7:0]  b,
  input  logic [7:0]  s,
  input  logic        overflow,
  input  logic        overflow_detected,
  input  logic [7:0]  adder_output,
  input  logic        overflow_signal
);
  let sum9 = {1'b0, a} + {1'b0, b};

  // Functional correctness
  ap_add_correct: assert property (@(posedge clk) disable iff (reset)
    adder_output == sum9[7:0]);

  ap_overflow_def: assert property (@(posedge clk) disable iff (reset)
    overflow_signal == ((a[7] == b[7]) && (a[7] != adder_output[7])));

  // Consistency constraints (redundant forms for clarity/robustness)
  ap_no_overflow_mixed_signs: assert property (@(posedge clk) disable iff (reset)
    (a[7] != b[7]) |-> !overflow_signal);

  ap_overflow_same_signs_equiv: assert property (@(posedge clk) disable iff (reset)
    (a[7] == b[7]) |-> (overflow_signal == (s[7] ^ a[7])));

  // Connectivity
  ap_connect_s:          assert property (@(posedge clk) disable iff (reset) s == adder_output);
  ap_connect_overflow:   assert property (@(posedge clk) disable iff (reset) overflow == overflow_signal);
  ap_indicator_passthru: assert property (@(posedge clk) disable iff (reset) overflow_detected == overflow);

  // No X/Z on outputs when inputs are clean
  ap_no_x_when_inputs_clean: assert property (@(posedge clk) disable iff (reset)
    (!$isunknown({a,b})) |-> !$isunknown({adder_output, s, overflow_signal, overflow, overflow_detected}));

  // Coverage: overflow/no-overflow scenarios and boundary cases
  cp_pos_overflow:    cover property (@(posedge clk) disable iff (reset) (a[7]==0 && b[7]==0 && overflow));
  cp_neg_overflow:    cover property (@(posedge clk) disable iff (reset) (a[7]==1 && b[7]==1 && overflow));
  cp_mixed_no_ovf:    cover property (@(posedge clk) disable iff (reset) (a[7]!=b[7] && !overflow));
  cp_boundary_pos:    cover property (@(posedge clk) disable iff (reset) (a==8'h7F && b==8'h01 && overflow && s[7]==1));
  cp_boundary_neg:    cover property (@(posedge clk) disable iff (reset) (a==8'h80 && b==8'hFF && overflow && s[7]==0));
  cp_zero_sum:        cover property (@(posedge clk) disable iff (reset) (sum9[7:0] == 8'h00));
endmodule

bind top_module top_module_sva u_top_module_sva (
  .clk(clk),
  .reset(reset),
  .a(a),
  .b(b),
  .s(s),
  .overflow(overflow),
  .overflow_detected(overflow_detected),
  .adder_output(adder_output),
  .overflow_signal(overflow_signal)
);