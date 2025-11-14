// SVA checker for mux4_1. Bind into the DUT and provide a sampling clk.
module mux4_1_sva (
  input logic clk,
  input logic X,
  input logic A0, A1, A2, A3,
  input logic S0, S1
);
  logic [1:0] sel = {S1,S0};
  default clocking cb @(posedge clk); endclocking

  // Functional correctness when select and selected input are known
  assert property ( (sel==2'b00 && !$isunknown({sel,A0})) |-> (X===A0) );
  assert property ( (sel==2'b01 && !$isunknown({sel,A1})) |-> (X===A1) );
  assert property ( (sel==2'b10 && !$isunknown({sel,A2})) |-> (X===A2) );
  assert property ( (sel==2'b11 && !$isunknown({sel,A3})) |-> (X===A3) );

  // Output updates to new selected input one cycle after select change (when all known)
  assert property (
    ($changed(sel) && !$isunknown({$past(sel),sel,A0,A1,A2,A3}))
    |-> ##1 ((sel==2'b00 && X===A0) ||
             (sel==2'b01 && X===A1) ||
             (sel==2'b10 && X===A2) ||
             (sel==2'b11 && X===A3))
  );

  // Unselected inputs must not affect X when select is stable (and selected input known)
  assert property (
    (sel==2'b00 && $past(sel)==2'b00 && !$isunknown({sel,$past(sel),A0,$past(A0)}) && $changed({A1,A2,A3}))
    |-> $stable(X)
  );
  assert property (
    (sel==2'b01 && $past(sel)==2'b01 && !$isunknown({sel,$past(sel),A1,$past(A1)}) && $changed({A0,A2,A3}))
    |-> $stable(X)
  );
  assert property (
    (sel==2'b10 && $past(sel)==2'b10 && !$isunknown({sel,$past(sel),A2,$past(A2)}) && $changed({A0,A1,A3}))
    |-> $stable(X)
  );
  assert property (
    (sel==2'b11 && $past(sel)==2'b11 && !$isunknown({sel,$past(sel),A3,$past(A3)}) && $changed({A0,A1,A2}))
    |-> $stable(X)
  );

  // X-propagation: if select is unknown and inputs disagree, output must be unknown
  assert property (
    ($isunknown(sel) && !(A0===A1 && A1===A2 && A2===A3)) |-> $isunknown(X)
  );

  // If all controls/data are known, output must be known
  assert property ( (!$isunknown({sel,A0,A1,A2,A3})) |-> !$isunknown(X) );

  // Coverage: exercise all select values
  cover property (sel==2'b00);
  cover property (sel==2'b01);
  cover property (sel==2'b10);
  cover property (sel==2'b11);

  // Coverage: propagation of 0/1 from each selected input
  cover property (sel==2'b00 && $rose(A0) && X==1'b1);
  cover property (sel==2'b00 && $fell(A0) && X==1'b0);
  cover property (sel==2'b01 && $rose(A1) && X==1'b1);
  cover property (sel==2'b01 && $fell(A1) && X==1'b0);
  cover property (sel==2'b10 && $rose(A2) && X==1'b1);
  cover property (sel==2'b10 && $fell(A2) && X==1'b0);
  cover property (sel==2'b11 && $rose(A3) && X==1'b1);
  cover property (sel==2'b11 && $fell(A3) && X==1'b0);
endmodule

// Bind example (provide a clock in your environment)
bind mux4_1 mux4_1_sva u_mux4_1_sva (
  .clk(clk),
  .X(X),
  .A0(A0), .A1(A1), .A2(A2), .A3(A3),
  .S0(S0), .S1(S1)
);