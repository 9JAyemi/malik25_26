// SVA for half_adder
module half_adder_sva(input logic a, b, sum, cout);

  // Trigger on any input edge; sample outputs after delta to avoid races
  default clocking cb @(posedge a or negedge a or posedge b or negedge b); endclocking

  // Functional correctness
  ap_func:   assert property (1'b1 |-> ##0 (sum === (a ^ b) && cout === (a & b)));

  // Outputs must be known when inputs are known
  ap_known:  assert property (!$isunknown({a,b}) |-> ##0 !$isunknown({sum,cout}));

  // sum and cout can never be 1 simultaneously (given known inputs)
  ap_mutex:  assert property (!$isunknown({a,b}) |-> ##0 !(sum && cout));

  // Truth table coverage
  cv_00: cover property ((a==0 && b==0) |-> ##0 (sum==0 && cout==0));
  cv_01: cover property ((a==0 && b==1) |-> ##0 (sum==1 && cout==0));
  cv_10: cover property ((a==1 && b==0) |-> ##0 (sum==1 && cout==0));
  cv_11: cover property ((a==1 && b==1) |-> ##0 (sum==0 && cout==1));

endmodule

// Bind into DUT
bind half_adder half_adder_sva sva_i(.a(a), .b(b), .sum(sum), .cout(cout));