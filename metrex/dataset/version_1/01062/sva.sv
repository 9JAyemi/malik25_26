// SVA package and binders for the provided DUTs.
// Focus: concise, complete functional checks, rail-tie checks, and key coverage.

package sky130_sva_pkg;

  function automatic logic a211oi_func (input logic A1, input logic A2,
                                        input logic B1, input logic C1);
    logic NMOS_TB, NMOS_BA, NMOS_AB, PMOS_BC;
    NMOS_TB = B1 & C1;
    NMOS_BA = A1 & B1;
    NMOS_AB = A1 & A2;
    PMOS_BC = B1 & C1;
    a211oi_func = (NMOS_AB | (NMOS_BA & ~PMOS_BC)) | (NMOS_TB & ~A2);
  endfunction

endpackage


module sky130_fd_sc_ms__a211oi_1_sva
(
  input logic A1, A2, B1, C1,
  input logic VPWR, VGND, VPB, VNB,
  input logic Y
);
  import sky130_sva_pkg::*;

  // Trigger on any relevant comb change
  `define EV_A211 (posedge A1 or negedge A1 or \
                    posedge A2 or negedge A2 or \
                    posedge B1 or negedge B1 or \
                    posedge C1 or negedge C1)

  // Functional equivalence
  assert property (@`EV_A211) (Y === a211oi_func(A1,A2,B1,C1));

  // Determinism: known inputs -> known output
  assert property (@`EV_A211) (!$isunknown({A1,A2,B1,C1})) |-> ##0 (!$isunknown(Y));

  // Rail sanity for body ties
  assert property (@(posedge VPWR or negedge VPWR or posedge VGND or negedge VGND
                     or posedge VPB or negedge VPB or posedge VNB or negedge VNB))
                   ((VPB === VPWR) and (VNB === VGND));

  // Basic input-space coverage
  cover property (@`EV_A211) ({A1,A2,B1,C1} == 4'b0000);
  cover property (@`EV_A211) ({A1,A2,B1,C1} == 4'b1111);
  cover property (@`EV_A211) ({A1,A2,B1,C1} == 4'b0101);
  cover property (@`EV_A211) ({A1,A2,B1,C1} == 4'b1010);

  `undef EV_A211
endmodule


module sky130_fd_sc_ms__inv_1_sva
(
  input logic A, VPWR, VGND, VPB, VNB,
  input logic Y
);
  import sky130_sva_pkg::*;

  `define EV_INV (posedge A or negedge A or \
                   posedge VPWR or negedge VPWR or \
                   posedge VGND or negedge VGND or \
                   posedge VNB  or negedge VNB)

  // Functional equivalence to instantiated a211oi mapping
  // Y == a211oi_func(A1=A, A2=VPWR, B1=VGND, C1=VNB)
  assert property (@`EV_INV)
    (Y === a211oi_func(A, VPWR, VGND, VNB));

  // With good rails, behavior reduces; also ensure determinism
  wire rails_good = (VPWR===1'b1 && VGND===1'b0 && VPB===1'b1 && VNB===1'b0);
  assert property (@`EV_INV) rails_good |-> ##0 (!$isunknown({A,Y}) && (Y === A));

  // Rail sanity for body ties
  assert property (@(posedge VPWR or negedge VPWR or posedge VGND or negedge VGND
                     or posedge VPB or negedge VPB or posedge VNB or negedge VNB))
                   ((VPB === VPWR) and (VNB === VGND));

  // Coverage: observe both Y transitions under good rails by toggling A
  cover property (@`EV_INV) rails_good and $rose(A) and ##0 $rose(Y);
  cover property (@`EV_INV) rails_good and $fell(A) and ##0 $fell(Y);

  `undef EV_INV
endmodule


module sky130_fd_sc_ms__nor2_1_sva
(
  input  logic A, B, VPWR, VGND, VPB, VNB,
  input  logic Y,
  input  logic w1
);
  import sky130_sva_pkg::*;

  `define EV_NOR (posedge A or negedge A or \
                   posedge B or negedge B or \
                   posedge VPWR or negedge VPWR or \
                   posedge VGND or negedge VGND or \
                   posedge VPB  or negedge VPB  or \
                   posedge VNB  or negedge VNB  or \
                   posedge w1   or negedge w1)

  // Check the intermediate a211oi instance
  assert property (@`EV_NOR)
    (w1 === a211oi_func(A, B, VPWR, VNB));

  // Check the final inverter instance
  assert property (@`EV_NOR)
    (Y === a211oi_func(w1, VPWR, VGND, VNB));

  // End-to-end compositional check
  assert property (@`EV_NOR)
    (Y === a211oi_func(a211oi_func(A,B,VPWR,VNB), VPWR, VGND, VNB));

  // With good rails, reduced behavior
  wire rails_good = (VPWR===1'b1 && VGND===1'b0 && VPB===1'b1 && VNB===1'b0);
  // Under good rails: w1 == A, Y == A
  assert property (@`EV_NOR) rails_good |-> ##0 (w1 === A && Y === A && !$isunknown({A,B,Y}));

  // Rail sanity for body ties
  assert property (@(posedge VPWR or negedge VPWR or posedge VGND or negedge VGND
                     or posedge VPB or negedge VPB or posedge VNB or negedge VNB))
                   ((VPB === VPWR) and (VNB === VGND));

  // Coverage: all A,B combos under good rails
  cover property (@`EV_NOR) rails_good && (A==0) && (B==0) && (Y==A);
  cover property (@`EV_NOR) rails_good && (A==0) && (B==1) && (Y==A);
  cover property (@`EV_NOR) rails_good && (A==1) && (B==0) && (Y==A);
  cover property (@`EV_NOR) rails_good && (A==1) && (B==1) && (Y==A);

  // Coverage: observe both Y transitions driven by A under good rails
  cover property (@`EV_NOR) rails_good and $rose(A) and ##0 $rose(Y);
  cover property (@`EV_NOR) rails_good and $fell(A) and ##0 $fell(Y);

  `undef EV_NOR
endmodule


// Bind SVA to DUTs
bind sky130_fd_sc_ms__a211oi_1 sky130_fd_sc_ms__a211oi_1_sva
  (.A1(A1), .A2(A2), .B1(B1), .C1(C1), .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB), .Y(Y));

bind sky130_fd_sc_ms__inv_1 sky130_fd_sc_ms__inv_1_sva
  (.A(A), .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB), .Y(Y));

bind sky130_fd_sc_ms__nor2_1 sky130_fd_sc_ms__nor2_1_sva
  (.A(A), .B(B), .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB), .Y(Y), .w1(w1));