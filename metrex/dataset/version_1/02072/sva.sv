// SVA bind module for mux_2to1
module mux_2to1_sva(input logic A, B, sel, Y);

  // Sample on any input transition
  default clocking cb @(posedge A or negedge A or
                        posedge B or negedge B or
                        posedge sel or negedge sel); endclocking

  // Functional correctness when inputs are known
  property p_func; !$isunknown({A,B,sel}) |-> (Y === (sel ? B : A)); endproperty
  assert property (p_func);

  // Pass-through and independence with stable select
  assert property ((sel==0 && $stable(sel) && $changed(A)) |-> (Y === A));
  assert property ((sel==0 && $stable(sel) && $stable(A) && $changed(B)) |-> $stable(Y));
  assert property ((sel==1 && $stable(sel) && $changed(B)) |-> (Y === B));
  assert property ((sel==1 && $stable(sel) && $stable(B) && $changed(A)) |-> $stable(Y));

  // Select edge behavior (combinational)
  assert property ($rose(sel) |-> (Y === B));
  assert property ($fell(sel) |-> (Y === A));

  // X-merge semantics when select is unknown
  assert property (($isunknown(sel) && !$isunknown({A,B}) && (A===B)) |-> (Y===A));
  assert property (($isunknown(sel) && !$isunknown({A,B}) && (A!==B)) |-> $isunknown(Y));

  // Coverage
  cover property (!$isunknown({A,B}) && sel==0 && Y===A);
  cover property (!$isunknown({A,B}) && sel==1 && Y===B);
  cover property ($rose(sel) && (A!=B));
  cover property ($rose(sel) && (A==B));
  cover property ($fell(sel) && (A!=B));
  cover property ($fell(sel) && (A==B));
  cover property (sel==0 && $changed(A));
  cover property (sel==1 && $changed(B));

endmodule

bind mux_2to1 mux_2to1_sva u_mux_2to1_sva (.*);