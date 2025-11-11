// SVA checker for sky130_fd_sc_hd__nor4bb
// Function spec: Y = ~(A | B | ~C_N | ~D_N)

module sky130_fd_sc_hd__nor4bb_sva (
  input logic Y,
  input logic A,
  input logic B,
  input logic C_N,
  input logic D_N
);

  // Sample on any edge of DUT signals (asynchronous combinational check)
  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B or
    posedge C_N or negedge C_N or
    posedge D_N or negedge D_N or
    posedge Y or negedge Y
  ); endclocking

  // Core functional equivalence
  assert property (disable iff ($isunknown({A,B,C_N,D_N}))
                   Y === ~(A | B | ~C_N | ~D_N))
    else $error("nor4bb functional mismatch");

  // Necessary conditions (any controlling 1 into the OR forces Y=0)
  assert property (A    |-> (Y==1'b0)) else $error("Y must be 0 when A=1");
  assert property (B    |-> (Y==1'b0)) else $error("Y must be 0 when B=1");
  assert property (!C_N |-> (Y==1'b0)) else $error("Y must be 0 when C_N=0");
  assert property (!D_N |-> (Y==1'b0)) else $error("Y must be 0 when D_N=0");

  // Sufficient condition (only case Y=1)
  assert property ((~A & ~B & C_N & D_N) |-> (Y==1'b1))
    else $error("Y must be 1 only when A=B=0, C_N=D_N=1");

  // Reduction when active-lows are high
  assert property ((C_N & D_N) |-> (Y === ~(A | B)))
    else $error("Reduction with C_N=D_N=1 failed");

  // Knownness: if inputs known, output must be known
  assert property (!$isunknown({A,B,C_N,D_N}) |-> !$isunknown(Y))
    else $error("Y is X/Z with known inputs");

  // No-glitch: if inputs stable, Y must remain stable
  assert property ($stable({A,B,C_N,D_N}) |=> $stable(Y))
    else $error("Glitch detected on Y while inputs stable");

  // Coverage
  cover property (~A & ~B &  C_N &  D_N ##0 (Y==1)); // only-1 case
  cover property ( A & ~B &  C_N &  D_N ##0 (Y==0));
  cover property (~A &  B &  C_N &  D_N ##0 (Y==0));
  cover property (~A & ~B & ~C_N &  D_N ##0 (Y==0));
  cover property (~A & ~B &  C_N & ~D_N ##0 (Y==0));
  cover property (($past(Y)===1'b0) && (Y===1'b1)); // Y rise
  cover property (($past(Y)===1'b1) && (Y===1'b0)); // Y fall

endmodule

// Bind into the DUT
bind sky130_fd_sc_hd__nor4bb sky130_fd_sc_hd__nor4bb_sva
  nor4bb_sva_i (.Y(Y), .A(A), .B(B), .C_N(C_N), .D_N(D_N));