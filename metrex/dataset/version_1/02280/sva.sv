// SVA for comparator. Bind this module to the DUT and provide clk/rst_n.
module comparator_sva #(
  parameter int WIDTH = 4
)(
  input logic                clk,
  input logic                rst_n,
  input logic [WIDTH-1:0]    A,
  input logic [WIDTH-1:0]    B,
  input logic                greater_than,
  input logic                less_than,
  input logic                equal_to,
  input logic                valid
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Basic sanity
  ap_inputs_known:  assert property (!$isunknown({A,B}));
  ap_outputs_known: assert property (!$isunknown({greater_than,less_than,equal_to,valid}));

  // Truth table (forward)
  ap_gt_truth: assert property ( (A >  B) |-> ##0 (greater_than && !less_than && !equal_to && valid) );
  ap_lt_truth: assert property ( (A <  B) |-> ##0 (less_than   && !greater_than && !equal_to && valid) );
  ap_eq_truth: assert property ( (A == B) |-> ##0 (equal_to    && !greater_than && !less_than && valid) );

  // Truth table (reverse)
  ap_gt_implies: assert property ( greater_than |-> ##0 (A >  B) );
  ap_lt_implies: assert property ( less_than    |-> ##0 (A <  B) );
  ap_eq_implies: assert property ( equal_to     |-> ##0 (A == B) );

  // Encoding/validity constraints
  ap_onehot_outputs: assert property ( $onehot({greater_than, less_than, equal_to}) );
  ap_valid_high:     assert property ( valid );
  ap_valid_equals_or:assert property ( valid == (greater_than || less_than || equal_to) );

  // Functional coverage
  cv_gt:       cover property ( (A >  B) && greater_than );
  cv_lt:       cover property ( (A <  B) && less_than );
  cv_eq:       cover property ( (A == B) && equal_to );
  cv_minmax_gt:cover property ( (A==WIDTH'(4'hF)) && (B==WIDTH'(4'h0)) && greater_than );
  cv_minmax_lt:cover property ( (A==WIDTH'(4'h0)) && (B==WIDTH'(4'hF)) && less_than );
  cv_zero_eq:  cover property ( (A==WIDTH'(0)) && (B==WIDTH'(0)) && equal_to );

endmodule

// Example bind (provide clk/rst_n from your environment):
// bind comparator comparator_sva #(.WIDTH(4))) u_comp_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));