// SVA for sky130_fd_sc_hd__o22ai
// Function: Y = ~((A1 | A2) & (B1 | B2))  == (~(A1|A2)) | (~(B1|B2))

module sky130_fd_sc_hd__o22ai_sva (
  input logic Y,
  input logic A1, A2, B1, B2
);
  logic gA, gB;
  assign gA = (A1 | A2);
  assign gB = (B1 | B2);

  // Combinational, 4-state-accurate checking and compact coverage
  always_comb begin
    // Functional equivalence (4-state exact)
    assert #0 (Y === ~(gA & gB))
      else $error("o22ai func mismatch: Y=%b A1=%b A2=%b B1=%b B2=%b", Y,A1,A2,B1,B2);

    // No X/Z on Y when inputs are all known
    if (!$isunknown({A1,A2,B1,B2}))
      assert #0 (!$isunknown(Y))
        else $error("o22ai X/Z on Y with known inputs");

    // Canonical cases (explicit)
    if (gA === 1'b1 && gB === 1'b1)
      assert #0 (Y === 1'b0) else $error("o22ai expected Y=0 when (A1|A2)=1 and (B1|B2)=1");
    if (gA === 1'b0 || gB === 1'b0)
      assert #0 (Y === 1'b1) else $error("o22ai expected Y=1 when either (A1|A2)=0 or (B1|B2)=0");

    // Functional coverage of all outcome classes
    cover (gA === 1'b1 && gB === 1'b1 && Y === 1'b0); // both groups 1 -> Y=0
    cover (gA === 1'b1 && gB === 1'b0 && Y === 1'b1);
    cover (gA === 1'b0 && gB === 1'b1 && Y === 1'b1);
    cover (gA === 1'b0 && gB === 1'b0 && Y === 1'b1);
  end
endmodule

bind sky130_fd_sc_hd__o22ai sky130_fd_sc_hd__o22ai_sva (.*);