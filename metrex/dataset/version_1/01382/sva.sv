// SVA for sky130_fd_sc_ls__o2111ai
// Function: Y = ~(C1 & B1 & D1 & (A1 | A2))

`ifndef SYNTHESIS
module sky130_fd_sc_ls__o2111ai_sva (
  input logic Y, A1, A2, B1, C1, D1
);

  // Sample on any input edge
  default clocking cb @(
    posedge A1 or negedge A1 or
    posedge A2 or negedge A2 or
    posedge B1 or negedge B1 or
    posedge C1 or negedge C1 or
    posedge D1 or negedge D1
  ); endclocking

  // Expected combinational value (4-state)
  logic exp;
  always_comb exp = ~(C1 & B1 & D1 & (A1 | A2));

  // Functional equivalence whenever determinable
  assert property ( !$isunknown(exp) |-> (Y === exp) )
    else $error("o2111ai: Y != ~(C1 & B1 & D1 & (A1|A2)) when determinable");

  // Controlling-0 on NAND inputs forces Y=1
  assert property ( (B1 === 1'b0) |-> (Y === 1'b1) )
    else $error("o2111ai: B1=0 must force Y=1");
  assert property ( (C1 === 1'b0) |-> (Y === 1'b1) )
    else $error("o2111ai: C1=0 must force Y=1");
  assert property ( (D1 === 1'b0) |-> (Y === 1'b1) )
    else $error("o2111ai: D1=0 must force Y=1");
  assert property ( (A1 === 1'b0 && A2 === 1'b0) |-> (Y === 1'b1) )
    else $error("o2111ai: A1=A2=0 must force Y=1");

  // All ones with OR true forces Y=0
  assert property ( (B1===1 && C1===1 && D1===1 && (A1===1 || A2===1)) |-> (Y===1'b0) )
    else $error("o2111ai: all gating=1 and (A1|A2)=1 must force Y=0");

  // No X/Z on Y when all inputs are known
  assert property ( !$isunknown({A1,A2,B1,C1,D1}) |-> !$isunknown(Y) )
    else $error("o2111ai: Y unknown while inputs are all known");

  // Coverage: key truth points and output activity
  cover property ( B1 && C1 && D1 && (A1 || A2) && (Y==1'b0) );            // NAND active -> Y=0
  cover property ( (A1==0 && A2==0) && (Y==1'b1) );                         // OR=0 -> Y=1
  cover property ( (B1==0) && (Y==1) );
  cover property ( (C1==0) && (Y==1) );
  cover property ( (D1==0) && (Y==1) );
  cover property ( B1 && C1 && D1 && (A1 ^ A2) && (Y==1'b0) );              // exactly one of A1/A2 high
  cover property ( $rose(Y) );
  cover property ( $fell(Y) );

endmodule

bind sky130_fd_sc_ls__o2111ai sky130_fd_sc_ls__o2111ai_sva
  u_o2111ai_sva (.Y(Y), .A1(A1), .A2(A2), .B1(B1), .C1(C1), .D1(D1));
`endif