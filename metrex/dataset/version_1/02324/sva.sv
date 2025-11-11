// SVA for comparator_4bit
module comparator_4bit_assert (
  input        clk,
  input  [3:0] in_a,
  input  [3:0] in_b,
  input        eq,
  input        gt,
  input        lt
);
  default clocking cb @(posedge clk); endclocking

  // Functional correctness with 1-cycle latency (sample inputs, check next cycle)
  property p_eq; logic [3:0] a,b; (a=in_a, b=in_b, 1'b1) ##1 (eq == (a==b)); endproperty
  property p_gt; logic [3:0] a,b; (a=in_a, b=in_b, 1'b1) ##1 (gt == (a>b));  endproperty
  property p_lt; logic [3:0] a,b; (a=in_a, b=in_b, 1'b1) ##1 (lt == (a<b));  endproperty

  assert property (p_eq);
  assert property (p_gt);
  assert property (p_lt);

  // Exactly one output asserted when outputs are known
  assert property (!$isunknown({eq,gt,lt}) |-> $onehot({eq,gt,lt}));

  // Outputs must be known one cycle after known inputs are sampled
  property p_known; logic [3:0] a,b; (a=in_a, b=in_b, !$isunknown({a,b})) ##1 !$isunknown({eq,gt,lt}); endproperty
  assert property (p_known);

  // Coverage: each relation and key corner cases
  cover property (eq);
  cover property (gt);
  cover property (lt);
  cover property ((in_a==4'h0 && in_b==4'h0) ##1 eq);
  cover property ((in_a==4'hF && in_b==4'hF) ##1 eq);
  cover property ((in_a==4'hF && in_b==4'h0) ##1 gt);
  cover property ((in_a==4'h0 && in_b==4'hF) ##1 lt);
  cover property ((in_a==in_b) ##1 (in_a>in_b) ##1 (in_a<in_b));
endmodule

bind comparator_4bit comparator_4bit_assert comparator_4bit_assert_i (.*);