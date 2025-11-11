// SVA for sky130_fd_sc_ls__o221ai
module sky130_fd_sc_ls__o221ai_sva (
  input logic A1, A2, B1, B2, C1,
  input logic Y
);
  logic ref_y;

  // Combinational functional correctness and X checks
  always_comb begin
    ref_y = ~((A1 | A2) & (B1 | B2) & C1);

    // Functional equivalence
    assert (Y === ref_y)
      else $error("o221ai func mismatch: A1=%b A2=%b B1=%b B2=%b C1=%b Y=%b ref=%b",
                  A1,A2,B1,B2,C1,Y,ref_y);

    // Equivalent DeMorgan form
    assert (Y === ((~C1) | (~(A1 | A2)) | (~(B1 | B2))))
      else $error("o221ai DeMorgan mismatch: A1=%b A2=%b B1=%b B2=%b C1=%b Y=%b",
                  A1,A2,B1,B2,C1,Y);

    // No unknown on Y when inputs are known
    if (!$isunknown({A1,A2,B1,B2,C1})) begin
      assert (!$isunknown(Y))
        else $error("o221ai X-prop: Y is X/Z with known inputs");
    end

    // Key controlling-value implications
    if (C1 === 1'b0)                               assert (Y === 1'b1) else $error("o221ai: C1=0 must force Y=1");
    if ((A1 === 1'b0) && (A2 === 1'b0))            assert (Y === 1'b1) else $error("o221ai: A1=A2=0 must force Y=1");
    if ((B1 === 1'b0) && (B2 === 1'b0))            assert (Y === 1'b1) else $error("o221ai: B1=B2=0 must force Y=1");
    if ((C1 === 1'b1) && ((A1 | A2)===1'b1) && ((B1 | B2)===1'b1))
                                                   assert (Y === 1'b0) else $error("o221ai: all high must force Y=0");
  end

  // Concise functional coverage (sampled on any input activity)
  cover property (@(A1 or A2 or B1 or B2 or C1)
                  (C1===1'b1) && ((A1|A2)===1'b1) && ((B1|B2)===1'b1) && (Y===1'b0)); // only case Y=0
  cover property (@(A1 or A2 or B1 or B2 or C1)
                  (C1===1'b0) && (Y===1'b1));                                         // Y=1 due to C1=0
  cover property (@(A1 or A2 or B1 or B2 or C1)
                  (A1===1'b0) && (A2===1'b0) && (Y===1'b1));                           // Y=1 due to A-group=0
  cover property (@(A1 or A2 or B1 or B2 or C1)
                  (B1===1'b0) && (B2===1'b0) && (Y===1'b1));                           // Y=1 due to B-group=0
endmodule

bind sky130_fd_sc_ls__o221ai sky130_fd_sc_ls__o221ai_sva sva_i (
  .A1(A1), .A2(A2), .B1(B1), .B2(B2), .C1(C1), .Y(Y)
);