// SVA for sky130_fd_sc_lp__o41ai
// Function: Y = ~((A1|A2|A3|A4) & B1)

module sky130_fd_sc_lp__o41ai_sva
(
  input logic Y,
  input logic A1, A2, A3, A4,
  input logic B1,
  // internal observability (optional but recommended)
  input logic or0_out,
  input logic nand0_out_Y
);

  // Core functional equivalence (bit-accurate, 4-state)
  always_comb begin
    assert (Y === ~(B1 & (A1 | A2 | A3 | A4)))
      else $error("o41ai func mismatch: Y=%b A={%b,%b,%b,%b} B1=%b", Y,A4,A3,A2,A1,B1);
  end

  // Structural consistency of internal nodes (guards against wiring/synthesis mishaps)
  always_comb begin
    assert (or0_out      === (A1 | A2 | A3 | A4))
      else $error("o41ai OR stage mismatch");
    assert (nand0_out_Y  === ~(B1 & or0_out))
      else $error("o41ai NAND stage mismatch");
    assert (Y            === nand0_out_Y)
      else $error("o41ai BUF stage mismatch");
  end

  // Strong implications and X-robustness
  always_comb begin
    // Dominance: B1==0 => Y==1 (even if A's are X)
    assert (B1 === 1'b0 -> Y === 1'b1)
      else $error("o41ai: B1=0 must force Y=1");
    // Dominance: all A's==0 => Y==1 (even if B1 is X)
    assert ((A1===1'b0 && A2===1'b0 && A3===1'b0 && A4===1'b0) -> Y === 1'b1)
      else $error("o41ai: all A=0 must force Y=1");
    // If Y known 0, both inputs to NAND must be 1
    if (!$isunknown(Y) && Y==1'b0)
      assert (B1===1'b1 && (A1|A2|A3|A4)===1'b1)
        else $error("o41ai: Y=0 requires B1=1 and some A=1");
    // Known inputs imply known output
    if (!($isunknown(B1) || $isunknown(A1|A2|A3|A4)))
      assert (!$isunknown(Y))
        else $error("o41ai: known inputs produced unknown Y");
  end

  // Lightweight functional coverage
  always_comb begin
    // Output value and toggles
    cover (Y === 1'b1);
    cover (Y === 1'b0);
    cover ($rose(Y));
    cover ($fell(Y));
    // Key scenarios
    cover (B1===1'b0 && Y===1'b1);
    cover (B1===1'b1 && (A1|A2|A3|A4)===1'b1 && Y===1'b0);
    cover (A1===1'b0 && A2===1'b0 && A3===1'b0 && A4===1'b0 && Y===1'b1);
    cover ((A1===1'b1 || A2===1'b1 || A3===1'b1 || A4===1'b1) && B1===1'b1 && Y===1'b0);
  end

endmodule

// Bind into DUT (connect internal nets for strongest checking)
bind sky130_fd_sc_lp__o41ai
  sky130_fd_sc_lp__o41ai_sva sva_i (
    .Y(Y),
    .A1(A1), .A2(A2), .A3(A3), .A4(A4),
    .B1(B1),
    .or0_out(or0_out),
    .nand0_out_Y(nand0_out_Y)
  );