// SVA for sky130_fd_sc_hd__a222oi
// Bind example (provide clk/rst_n in TB):
// bind sky130_fd_sc_hd__a222oi sky130_fd_sc_hd__a222oi_sva u_sva(.*,.clk(clk),.rst_n(rst_n));

module sky130_fd_sc_hd__a222oi_sva (
  input logic clk, rst_n,
  input logic A1, A2, B1, B2, C1, C2,
  input logic Y,
  input logic VPB, VPWR, VGND, VNB
);

  // Clocking and gating
  default clocking cb @ (posedge clk); endclocking
  let power_good = (VPWR===1'b1) && (VGND===1'b0) && (VPB===VPWR) && (VNB===VGND);
  default disable iff (!rst_n || !power_good);

  // Known-ness and golden function
  let known_in = !$isunknown({A1,A2,B1,B2,C1,C2});
  let fY =
       (A1 && !A2) ? 1'b1 :
       (!A1 && A2) ? 1'b0 :
       (!A1 && !A2 && (B1 || C1)) ? 1'b1 :
       (!A1 && !A2 && (B2 || C2)) ? 1'b0 :
       (A1 && A2 && B1 && C1) ? 1'b1 :
       (A1 && A2 && B2 && C2) ? 1'b0 :
       1'b0;

  // Functional correctness and 4-state cleanliness
  assert property ( known_in |-> (Y === fY) )
    else $error("Y mismatch functional spec");
  assert property ( known_in |-> !$isunknown(Y) )
    else $error("Y is X/Z with known inputs");

  // Purely combinational: no hidden state
  assert property ( $stable({A1,A2,B1,B2,C1,C2}) |=> $stable(Y) )
    else $error("Y changed without input change");

  // Branch coverage (exercise each decision path and the default)
  cover property ( known_in && (A1 && !A2) && (Y==1) );
  cover property ( known_in && (!A1 && A2) && (Y==0) );
  cover property ( known_in && (!A1 && !A2) && (B1 || C1) && (Y==1) );
  cover property ( known_in && (!A1 && !A2) && !(B1 || C1) && (B2 || C2) && (Y==0) );
  cover property ( known_in && (A1 && A2 && B1 && C1) && (Y==1) );
  cover property ( known_in && (A1 && A2) && !(B1 && C1) && (B2 && C2) && (Y==0) );
  cover property ( known_in &&
                   !(A1 && !A2) &&
                   !(!A1 && A2) &&
                   !(!A1 && !A2 && (B1 || C1)) &&
                   !(!A1 && !A2 && (B2 || C2)) &&
                   !(A1 && A2 && B1 && C1) &&
                   !(A1 && A2 && B2 && C2) &&
                   (Y==0) );

  // Output polarity coverage
  cover property ( known_in && Y==1 );
  cover property ( known_in && Y==0 );
  cover property ( known_in ##1 (Y==0) ##1 (Y==1) );
  cover property ( known_in ##1 (Y==1) ##1 (Y==0) );

endmodule