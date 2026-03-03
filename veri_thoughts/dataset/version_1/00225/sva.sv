// SVA bind file for top_module and submodules
// Concise, combinationally-clocked checks and coverage

`ifndef SVA_TOP_MODULE
`define SVA_TOP_MODULE
`ifndef SYNTHESIS

// Top-level checker (bind into top_module)
module top_module_sva;
  // Sample on any A/B activity; ##0 to evaluate after delta propagation
  default clocking cb @ (A or B); endclocking
  wire inputs_known = !$isunknown({A,B});

  // Comparator correctness and exclusivity at top
  a_cmp_eq:     assert property (disable iff (!inputs_known) ##0 (eq == ($signed(A) == $signed(B))));
  a_cmp_gt:     assert property (disable iff (!inputs_known) ##0 (gt == ($signed(A) >  $signed(B))));
  a_cmp_lt:     assert property (disable iff (!inputs_known) ##0 (lt == ($signed(A) <  $signed(B))));
  a_cmp_onehot: assert property (disable iff (!inputs_known) ##0 $onehot({eq,gt,lt}));

  // Mux selection correctness
  a_mux_eq: assert property (disable iff (!inputs_known) ##0 (eq |-> (out == sum)));
  a_mux_gt: assert property (disable iff (!inputs_known) ##0 (gt |-> (out == A)));
  a_mux_lt: assert property (disable iff (!inputs_known) ##0 (lt |-> (out == B)));

  // Overflow passthrough from adder
  a_oflow_passthru: assert property (disable iff (!inputs_known) ##0 (overflow == overflow_adder));

  // Top-level functional coverage
  c_eq:          cover property (disable iff (!inputs_known) ##0 eq);
  c_gt:          cover property (disable iff (!inputs_known) ##0 gt);
  c_lt:          cover property (disable iff (!inputs_known) ##0 lt);
  c_mux_eq:      cover property (disable iff (!inputs_known) ##0 (eq && (out == sum)));
  c_mux_gt:      cover property (disable iff (!inputs_known) ##0 (gt && (out == A)));
  c_mux_lt:      cover property (disable iff (!inputs_known) ##0 (lt && (out == B)));
  c_eq_overflow: cover property (disable iff (!inputs_known) ##0 (eq && overflow));
endmodule
bind top_module top_module_sva tps();

// Signed adder checker (bind into signed_adder)
module signed_adder_sva;
  default clocking cb @ (A or B); endclocking
  wire inputs_known = !$isunknown({A,B});

  // Out equals 4-bit two's-complement sum (wrapping)
  a_sum: assert property (disable iff (!inputs_known) ##0 (out == (A + B)));

  // Two's-complement overflow detection
  a_overflow: assert property (disable iff (!inputs_known) ##0
                               (overflow == ((A[3] == B[3]) && ((A + B)[3] != A[3]))));

  // Adder coverage
  c_overflow_pos: cover property (disable iff (!inputs_known) ##0 (overflow && (A[3]==0) && (B[3]==0)));
  c_overflow_neg: cover property (disable iff (!inputs_known) ##0 (overflow && (A[3]==1) && (B[3]==1)));
  c_no_overflow:  cover property (disable iff (!inputs_known) ##0 !overflow);
endmodule
bind signed_adder signed_adder_sva sas();

// Signed comparator checker (bind into signed_comparator)
module signed_comparator_sva;
  default clocking cb @ (A or B); endclocking
  wire inputs_known = !$isunknown({A,B});

  a_eq:     assert property (disable iff (!inputs_known) ##0 (eq == ($signed(A) == $signed(B))));
  a_gt:     assert property (disable iff (!inputs_known) ##0 (gt == ($signed(A) >  $signed(B))));
  a_lt:     assert property (disable iff (!inputs_known) ##0 (lt == ($signed(A) <  $signed(B))));
  a_onehot: assert property (disable iff (!inputs_known) ##0 $onehot({eq,gt,lt}));

  // Relation coverage
  c_eq: cover property (disable iff (!inputs_known) ##0 eq);
  c_gt: cover property (disable iff (!inputs_known) ##0 gt);
  c_lt: cover property (disable iff (!inputs_known) ##0 lt);
endmodule
bind signed_comparator signed_comparator_sva scs();

`endif
`endif