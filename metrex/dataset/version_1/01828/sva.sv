// SVA for sky130_fd_sc_hdll__o21bai
// Function: Y = ~( (~B1_N) & (A1 | A2) ) = B1_N | (~A1 & ~A2)

module sky130_fd_sc_hdll__o21bai_sva (
  input logic A1,
  input logic A2,
  input logic B1_N,
  input logic Y
);

  // Sample on any input edge (purely combinational cell)
  default clocking cb @(posedge A1 or negedge A1
                       or posedge A2 or negedge A2
                       or posedge B1_N or negedge B1_N); endclocking

  // Functional equivalence when inputs are known
  assert property ( !$isunknown({A1,A2,B1_N})
                    |-> (Y === ~( (~B1_N) & (A1 | A2) )) )
    else $error("o21bai func mismatch");

  // Key implications (concise truth-corner checks)
  assert property ( B1_N |-> Y )
    else $error("B1_N=1 must force Y=1");
  assert property ( (!B1_N && (A1 || A2)) |-> !Y )
    else $error("~B1_N & (A1|A2) must force Y=0");
  assert property ( (!A1 && !A2) |-> Y )
    else $error("A1=A2=0 must force Y=1");

  // Functional truth-table coverage (8 input combos with expected Y)
  cover property ( A1==0 && A2==0 && B1_N==0 && Y==1 );
  cover property ( A1==0 && A2==0 && B1_N==1 && Y==1 );
  cover property ( A1==0 && A2==1 && B1_N==0 && Y==0 );
  cover property ( A1==0 && A2==1 && B1_N==1 && Y==1 );
  cover property ( A1==1 && A2==0 && B1_N==0 && Y==0 );
  cover property ( A1==1 && A2==0 && B1_N==1 && Y==1 );
  cover property ( A1==1 && A2==1 && B1_N==0 && Y==0 );
  cover property ( A1==1 && A2==1 && B1_N==1 && Y==1 );

  // Output toggle coverage
  cover property ( $rose(Y) );
  cover property ( $fell(Y) );

endmodule

bind sky130_fd_sc_hdll__o21bai sky130_fd_sc_hdll__o21bai_sva sva_i (.A1(A1), .A2(A2), .B1_N(B1_N), .Y(Y));