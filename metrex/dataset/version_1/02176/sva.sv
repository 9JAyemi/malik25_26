// SVA for sky130_fd_sc_ls__a2bb2o
// Function: X = (~A1_N & ~A2_N) | (B1 & B2)

module sky130_fd_sc_ls__a2bb2o_sva (
  input logic X,
  input logic A1_N,
  input logic A2_N,
  input logic B1,
  input logic B2
);

  // Power pins exist in DUT scope; check once
  initial begin
    assert (VPWR === 1'b1) else $error("VPWR not 1");
    assert (VGND === 1'b0) else $error("VGND not 0");
    assert (VPB  === 1'b1) else $error("VPB not 1");
    assert (VNB  === 1'b0) else $error("VNB not 0");
  end

  // Functional equivalence when inputs are all known
  always_comb begin
    bit all_known = !$isunknown({A1_N,A2_N,B1,B2});
    if (all_known) begin
      assert (X === ((~A1_N & ~A2_N) | (B1 & B2)))
        else $error("Func mismatch: X=%b A1_N=%b A2_N=%b B1=%b B2=%b",
                    X,A1_N,A2_N,B1,B2);
      assert (!$isunknown(X)) else $error("X unknown with known inputs");
    end
  end

  // Dominating term checks (robust to X on the other side)
  always_comb begin
    if (B1===1'b1 && B2===1'b1)
      assert (X===1'b1) else $error("AND term 1 should force X=1");

    if (A1_N===1'b0 && A2_N===1'b0)
      assert (X===1'b1) else $error("NOR term 1 should force X=1");

    if ((B1===1'b0 || B2===1'b0) && (A1_N===1'b1 || A2_N===1'b1))
      assert (X===1'b0) else $error("Both terms 0 should force X=0");
  end

  // Structural toggling coverage
  cover property (@(posedge A1_N) 1);
  cover property (@(negedge A1_N) 1);
  cover property (@(posedge A2_N) 1);
  cover property (@(negedge A2_N) 1);
  cover property (@(posedge B1)   1);
  cover property (@(negedge B1)   1);
  cover property (@(posedge B2)   1);
  cover property (@(negedge B2)   1);
  cover property (@(posedge X)    1);
  cover property (@(negedge X)    1);

  // Functional scenario coverage
  cover property ( (B1===1 && B2===1) && (X===1) );                 // AND path
  cover property ( (A1_N===0 && A2_N===0) && (X===1) );             // NOR path
  cover property ( (A1_N===0 && A2_N===0 && B1===1 && B2===1) &&
                   (X===1) );                                       // both terms 1
  cover property ( (B1===0 || B2===0) && (A1_N===1 || A2_N===1) &&
                   (X===0) );                                       // both terms 0

  // X-masking coverage (1 dominates OR)
  cover property ( (B1===1 && B2===1) && $isunknown({A1_N,A2_N}) && (X===1) );
  cover property ( (A1_N===0 && A2_N===0) && $isunknown({B1,B2}) && (X===1) );

endmodule

// Bind into the DUT
bind sky130_fd_sc_ls__a2bb2o sky130_fd_sc_ls__a2bb2o_sva sva_i (.X(X), .A1_N(A1_N), .A2_N(A2_N), .B1(B1), .B2(B2));