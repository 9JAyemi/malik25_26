// SVA for sky130_fd_sc_ms__o211ai: Y = ~(C1 & (A1 | A2) & B1)

module sky130_fd_sc_ms__o211ai_sva (
  input logic A1, A2, B1, C1,
  input logic Y
);

  // Sample on any input edge; check after ##0 to avoid race with comb updates
  default clocking cb @(posedge A1 or negedge A1
                      or posedge A2 or negedge A2
                      or posedge B1 or negedge B1
                      or posedge C1 or negedge C1); endclocking

  // Functional equivalence
  assert property (1'b1 |-> ##0 (Y === ~(C1 & (A1 | A2) & B1)));

  // Strong decomposition checks
  assert property ((B1===1'b0)                                       |-> ##0 (Y===1'b1));
  assert property ((C1===1'b0)                                       |-> ##0 (Y===1'b1));
  assert property ((B1===1'b1 && C1===1'b1 && A1===1'b0 && A2===1'b0)|-> ##0 (Y===1'b1));
  assert property ((B1===1'b1 && C1===1'b1 && (A1===1'b1 || A2===1'b1)) |-> ##0 (Y===1'b0));

  // Known-inputs imply known-output
  assert property ((!$isunknown({A1,A2,B1,C1})) |-> ##0 (!$isunknown(Y)));

  // Coverage: exercise all functional reasons for Y=0 and Y=1
  cover  property (B1 && C1 && (A1||A2)        ##0 (Y==1'b0)); // NAND drives low
  cover  property (!B1                         ##0 (Y==1'b1)); // B1=0 forces high
  cover  property (!C1                         ##0 (Y==1'b1)); // C1=0 forces high
  cover  property (B1 && C1 && !A1 && !A2      ##0 (Y==1'b1)); // OR=0 with enables=1
endmodule

bind sky130_fd_sc_ms__o211ai sky130_fd_sc_ms__o211ai_sva sva (.*);