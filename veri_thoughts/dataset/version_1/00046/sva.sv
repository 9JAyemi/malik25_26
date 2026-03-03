// SVA for o311ai: Y = (A2 | (A1 & B1)) & ~A3 & C1
// Bind-only, concise, high-quality functional checks + key coverage

module o311ai_sva (
  input logic A1, A2, A3, B1, C1,
  input logic Y
);
  // Trigger on any input edge
  default clocking cb @(
    posedge A1 or negedge A1 or
    posedge A2 or negedge A2 or
    posedge A3 or negedge A3 or
    posedge B1 or negedge B1 or
    posedge C1 or negedge C1
  ); endclocking

  // No-X on output when inputs are known
  assert property (!$isunknown({A1,A2,A3,B1,C1}) |-> !$isunknown(Y))
    else $error("o311ai: Y is X/Z with known inputs");

  // Full functional equivalence when inputs are known
  assert property (!$isunknown({A1,A2,A3,B1,C1})
                   |-> (Y == ((A2 | (A1 & B1)) & ~A3 & C1)))
    else $error("o311ai: Functional mismatch");

  // Strong gating checks that are independent of other inputs
  assert property (A3 === 1'b1 |-> Y === 1'b0)
    else $error("o311ai: A3=1 must force Y=0");
  assert property (C1 === 1'b0 |-> Y === 1'b0)
    else $error("o311ai: C1=0 must force Y=0");

  // Path-specific correctness under enable (C1=1, ~A3=1)
  assert property ((C1==1 && A3==0 && A2==1) |-> (Y==1))
    else $error("o311ai: A2 path should drive Y=1");
  assert property ((C1==1 && A3==0 && A2==0 && (A1 & B1)==1) |-> (Y==1))
    else $error("o311ai: A1&B1 path should drive Y=1");
  assert property ((C1==1 && A3==0 && A2==0 && (A1 & B1)==0) |-> (Y==0))
    else $error("o311ai: Disabled lower term should keep Y=0");

  // Minimal, meaningful coverage
  cover property (C1 && !A3 && A2 && Y);                 // Y=1 via A2 path
  cover property (C1 && !A3 && !A2 && A1 && B1 && Y);    // Y=1 via A1&B1 path
  cover property (!Y && A3);                             // Y blocked by A3
  cover property (!Y && !C1);                            // Y blocked by C1
  cover property (C1 && !A3 && !A2 && !(A1 && B1) && !Y);// Y=0 when both terms low
  cover property ($rose(Y));
  cover property ($fell(Y));
endmodule

bind o311ai o311ai_sva i_o311ai_sva (.A1(A1),.A2(A2),.A3(A3),.B1(B1),.C1(C1),.Y(Y));