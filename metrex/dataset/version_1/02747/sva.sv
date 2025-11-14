// SVA bind module for my_nor2
module my_nor2_sva (
  input logic Y,
  input logic A,
  input logic B_N,
  input logic VPWR,
  input logic VGND,
  input logic VPB,
  input logic VNB
);
  // Clocking: check on any relevant edge
  default clocking cb @(posedge A or negedge A or posedge B_N or negedge B_N or posedge Y or negedge Y); endclocking

  // Power-good
  function automatic bit pwr_good;
    return (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0);
  endfunction
  default disable iff (!pwr_good());

  // Supplies must be correctly tied
  assert property (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0)
    else $error("Power pins not tied correctly");

  // Functional correctness (dominance and full equivalence when inputs known)
  assert property (A===1'b1 |-> Y===1'b0) else $error("A=1 must force Y=0");
  assert property (B_N===1'b1 |-> Y===1'b0) else $error("B_N=1 must force Y=0");
  assert property (A===1'b0 && B_N===1'b0 |-> Y===1'b1) else $error("A=0,B_N=0 must force Y=1");
  assert property (!$isunknown({A,B_N}) |-> (Y===~(A|B_N)))
    else $error("Y != ~(A|B_N) when inputs known");

  // Sanity: no Z on output when powered
  assert property (Y!==1'bz) else $error("Y is high-Z");

  // Functional coverage: truth table and output edges
  cover property (A==1'b0 && B_N==1'b0 && Y==1'b1);
  cover property (A==1'b0 && B_N==1'b1 && Y==1'b0);
  cover property (A==1'b1 && B_N==1'b0 && Y==1'b0);
  cover property (A==1'b1 && B_N==1'b1 && Y==1'b0);
  cover property ($rose(Y));
  cover property ($fell(Y));
endmodule

// Bind to DUT
bind my_nor2 my_nor2_sva u_my_nor2_sva (.*);