// SVA for HalfAdder
// Bind these assertions to the DUT; no changes to DUT required.

module HalfAdder_sva(input logic A, Cin, Sum, Cout);
  // Sample on any input edge
  default clocking cb @(posedge A or negedge A or posedge Cin or negedge Cin); endclocking

  function bit iknown(); return !$isunknown({A, Cin}); endfunction
  function bit oknown(); return !$isunknown({Sum, Cout}); endfunction

  // Functional correctness and X-propagation
  assert property (iknown() |-> ##0 oknown());
  assert property (iknown() |-> ##0 (Sum == (A ^ Cin) && Cout == (A & Cin)));

  // At most one of {Sum,Cout} is 1 (and none are X when inputs known)
  assert property (iknown() |-> ##0 $onehot0({Sum, Cout}));

  // Outputs only change when inputs change
  assert property (@(posedge Sum or negedge Sum or posedge Cout or negedge Cout)
                   iknown() && ($changed(A) || $changed(Cin)));

  // Truth-table coverage (with correctness)
  cover property (iknown() && A==0 && Cin==0 && Sum==0 && Cout==0);
  cover property (iknown() && A==0 && Cin==1 && Sum==1 && Cout==0);
  cover property (iknown() && A==1 && Cin==0 && Sum==1 && Cout==0);
  cover property (iknown() && A==1 && Cin==1 && Sum==0 && Cout==1);

  // Toggle coverage on each input with the other held stable
  cover property (iknown() && $rose(A)  && $stable(Cin));
  cover property (iknown() && $fell(A)  && $stable(Cin));
  cover property (iknown() && $rose(Cin) && $stable(A));
  cover property (iknown() && $fell(Cin) && $stable(A));
endmodule

bind HalfAdder HalfAdder_sva sva(.A(A), .Cin(Cin), .Sum(Sum), .Cout(Cout));