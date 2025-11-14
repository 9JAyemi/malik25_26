// SVA for adder: concise, high-quality checks and coverage.
// Bind this to the DUT. No external clock/reset required; assertions sample on signal changes.
// Uses ##0 to evaluate after combinational updates settle in the current timestep.

module adder_sva (
  input logic [7:0] a,
  input logic [7:0] b,
  input logic [7:0] sum,
  input logic       carry
);

  // Inputs should be known (no X/Z)
  ap_inputs_known: assert property (@(a or b) ##0 !$isunknown({a,b}))
    else $error("adder: inputs contain X/Z");

  // Outputs should be known when inputs are known
  ap_outputs_known: assert property (@(a or b or sum or carry)
                                     (!$isunknown({a,b})) |-> ##0 !$isunknown({sum,carry}))
    else $error("adder: outputs contain X/Z with known inputs");

  // Functional correctness: 9-bit sum equals a+b
  ap_add_correct: assert property (@(a or b or sum or carry)
                                   (!$isunknown({a,b})) |-> ##0 ({carry,sum} == ({1'b0,a}+{1'b0,b})))
    else $error("adder: {carry,sum} != a+b");

  // Basic functional coverage on interesting corner cases (sampled on input changes)
  cp_no_carry:     cover property (@(a or b) ##0 (carry==1'b0 && {carry,sum} == ({1'b0,a}+{1'b0,b})));
  cp_with_carry:   cover property (@(a or b) ##0 (carry==1'b1 && {carry,sum} == ({1'b0,a}+{1'b0,b})));
  cp_sum_255:      cover property (@(a or b) ##0 (({1'b0,a}+{1'b0,b}) == 9'h0FF && carry==1'b0 && sum==8'hFF));
  cp_sum_256:      cover property (@(a or b) ##0 (({1'b0,a}+{1'b0,b}) == 9'h100 && carry==1'b1 && sum==8'h00));
  cp_zero_zero:    cover property (@(a or b) ##0 (a==8'h00 && b==8'h00 && carry==1'b0 && sum==8'h00));
  cp_max_max:      cover property (@(a or b) ##0 (a==8'hFF && b==8'hFF && carry==1'b1 && sum==8'hFE));

endmodule

// Bind into the DUT (ports match by name)
bind adder adder_sva u_adder_sva (.*);