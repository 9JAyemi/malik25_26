// SVA for sky130_fd_sc_lp__and4bb
// Function: X = (~A_N & ~B_N & C & D)

module sky130_fd_sc_lp__and4bb_sva
(
  input logic A_N,
  input logic B_N,
  input logic C,
  input logic D,
  input logic X
);
  logic expr;
  always_comb expr = (~A_N) & (~B_N) & C & D;

  // Functional equivalence (4-state exact)
  always_comb begin
    assert (X === expr)
      else $error("X must equal ~A_N & ~B_N & C & D");
  end

  // X==1 implies all enables true (robust to Xs on inputs)
  always_comb if (X === 1'b1) assert (expr === 1'b1)
    else $error("X==1 requires ~A_N & ~B_N & C & D");

  // Controlling values force X==0 irrespective of other inputs
  always_comb begin
    if (A_N === 1'b1) assert (X === 1'b0) else $error("A_N=1 must force X=0");
    if (B_N === 1'b1) assert (X === 1'b0) else $error("B_N=1 must force X=0");
    if (C   === 1'b0) assert (X === 1'b0) else $error("C=0 must force X=0");
    if (D   === 1'b0) assert (X === 1'b0) else $error("D=0 must force X=0");
  end

  // If inputs are fully known, X must be known
  always_comb if (!$isunknown({A_N,B_N,C,D})) assert (!$isunknown(X))
    else $error("X must be 0/1 when inputs are known");

  // Coverage
  cover property (expr && X==1);                           // X high case
  cover property (A_N && !B_N && C && D && X==0);          // A_N gating
  cover property (B_N && !A_N && C && D && X==0);          // B_N gating
  cover property (!A_N && !B_N && !C && D && X==0);        // C gating
  cover property (!A_N && !B_N && C && !D && X==0);        // D gating
  cover property (A_N && B_N && C && D && X==0);           // both A_N/B_N high
  cover property (@(posedge X) 1);                         // X rise
  cover property (@(negedge X) 1);                         // X fall
endmodule

// Bind to DUT
bind sky130_fd_sc_lp__and4bb sky130_fd_sc_lp__and4bb_sva sva_i(.A_N(A_N), .B_N(B_N), .C(C), .D(D), .X(X));