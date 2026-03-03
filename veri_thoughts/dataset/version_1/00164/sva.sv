// SVA for and4. Bind this file alongside the DUT.

module and4_sva (
  input  logic A, B, C, D,
  input  logic X,
  input  logic temp1, temp2,
  input  logic VPWR, VGND, VPB, VNB
);

  // Functional correctness (4-state accurate)
  always_comb begin
    assert #0 (X === (A & B & C & D))
      else $error("and4: X must equal A&B&C&D");
  end

  // Structural nets match gate decomposition
  always_comb begin
    assert #0 (temp1 === (A & B & C))
      else $error("and4: temp1 mismatch");
    assert #0 (temp2 === (temp1 & C & D))
      else $error("and4: temp2 mismatch");
    assert #0 (X === temp2)
      else $error("and4: X != temp2");
  end

  // Controlling value and implication checks
  always_comb begin
    if ((A === 1'b0) || (B === 1'b0) || (C === 1'b0) || (D === 1'b0))
      assert #0 (X === 1'b0)
        else $error("and4: X must be 0 when any input is 0");
    if (X === 1'b1)
      assert #0 ((A===1'b1)&&(B===1'b1)&&(C===1'b1)&&(D===1'b1))
        else $error("and4: X==1 implies all inputs==1");
    if (!$isunknown({A,B,C,D}))
      assert #0 (!$isunknown(X))
        else $error("and4: X unknown while inputs are known");
  end

  // Power/ground rails sanity
  initial begin
    assert (VPWR === 1'b1) else $error("and4: VPWR != 1");
    assert (VPB  === 1'b1) else $error("and4: VPB  != 1");
    assert (VGND === 1'b0) else $error("and4: VGND != 0");
    assert (VNB  === 1'b0) else $error("and4: VNB  != 0");
  end

  // Minimal functional coverage
  // Event: any input edge
  // X high/low observed
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D) X === 1'b1);
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D) X === 1'b0);
  // Extremes
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D) ({A,B,C,D,X} === 5'b11111));
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D) ({A,B,C,D,X} === 5'b00000));
  // Single-zero cases (others 1, X=0)
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
                  (A===1'b0 && B===1'b1 && C===1'b1 && D===1'b1 && X===1'b0));
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
                  (A===1'b1 && B===1'b0 && C===1'b1 && D===1'b1 && X===1'b0));
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
                  (A===1'b1 && B===1'b1 && C===1'b0 && D===1'b1 && X===1'b0));
  cover property (@(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
                  (A===1'b1 && B===1'b1 && C===1'b1 && D===1'b0 && X===1'b0));
  // Output toggles
  cover property (@(posedge X) 1);
  cover property (@(negedge X) 1);

endmodule

// Bind into every instance of and4
bind and4 and4_sva u_and4_sva (
  .A(A), .B(B), .C(C), .D(D),
  .X(X),
  .temp1(temp1), .temp2(temp2),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);