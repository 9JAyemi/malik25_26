// SVA for max_value
// Checks functional correctness, no spurious changes, and provides concise branch coverage.

module max_value_sva #(parameter int W = 8)
(
  input logic [W-1:0] A,
  input logic [W-1:0] B,
  input logic [W-1:0] max
);

  // Sample on any input change; use ##0 to observe post-comb-updated output.
  default clocking cb @(A or B); endclocking

  // Functional spec: max = A if A>B, else B if B>A, else 0 (when A==B).
  property p_func;
    disable iff ($isunknown({A,B}))
    1 |-> ##0 ( max == (A>B ? A : (B>A ? B : '0)) );
  endproperty
  a_func: assert property (p_func);

  // Branch-specific checks (also aid debug)
  a_gt_b: assert property ( disable iff ($isunknown({A,B})) (A>B)  |-> ##0 (max==A) );
  b_gt_a: assert property ( disable iff ($isunknown({A,B})) (B>A)  |-> ##0 (max==B) );
  a_eq_b: assert property ( disable iff ($isunknown({A,B})) (A==B) |-> ##0 (max=='0) );

  // No spurious output change without an input change.
  property p_no_spurious;
    @(A or B or max)
    disable iff ($isunknown({A,B}))
    $changed(max) |-> ($changed(A) || $changed(B));
  endproperty
  a_no_spurious: assert property (p_no_spurious);

  // Ensure output is known whenever inputs are known.
  a_known: assert property ( disable iff ($isunknown({A,B})) ##0 !$isunknown(max) );

  // Coverage: hit all three behavioral branches.
  c_a_gt_b: cover property ( (A>B)  ##0 (max==A) );
  c_b_gt_a: cover property ( (B>A)  ##0 (max==B) );
  c_a_eq_b: cover property ( (A==B) ##0 (max=='0) );

endmodule

// Bind into the DUT
bind max_value max_value_sva #(.W(8)) max_value_sva_i ( .A(A), .B(B), .max(max) );