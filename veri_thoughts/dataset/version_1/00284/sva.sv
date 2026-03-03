// SVA checker for sky130_fd_sc_ls__a211oi
// Function: Y = (A1 & A2) | ((!A1 & !A2) & (B1 ^ C1))

module sky130_fd_sc_ls__a211oi_sva (
  input logic Y,
  input logic A1, A2, B1, C1,
  input logic VPWR, VGND, VPB, VNB
);

  function automatic logic fy (logic A1, A2, B1, C1);
    fy = (A1 & A2) | ((~A1 & ~A2) & (B1 ^ C1));
  endfunction

  logic rails_known, pgood, inputs_known;
  assign rails_known  = !$isunknown({VPWR,VGND,VPB,VNB});
  assign pgood        = (VPWR===1'b1) && (VGND===1'b0) && (VPB===1'b1) && (VNB===1'b0);
  assign inputs_known = !$isunknown({A1,A2,B1,C1});

  // Power-rail sanity (assert when rails are known)
  always_comb begin
    if (rails_known) begin
      assert (VPWR===1'b1) else $error("a211oi: VPWR != 1");
      assert (VGND===1'b0) else $error("a211oi: VGND != 0");
      assert (VPB ===1'b1) else $error("a211oi: VPB  != 1");
      assert (VNB ===1'b0) else $error("a211oi: VNB  != 0");
    end
  end

  // Core functional checks (combinational, power-good, known inputs)
  always_comb begin
    if (pgood && inputs_known) begin
      assert (Y === fy(A1,A2,B1,C1))
        else $error("a211oi: Y mismatch exp=%0b got=%0b (A1A2B1C1=%0b%0b%0b%0b)",
                    fy(A1,A2,B1,C1), Y, A1, A2, B1, C1);
      assert (!$isunknown(Y)) else $error("a211oi: Y is X with known inputs");
    end

    // Helpful localized implications (concise, aid debug)
    if (pgood && A1 && A2)                assert (Y===1'b1) else $error("a211oi: A1&A2 -> Y should be 1");
    if (pgood && !A1 && !A2)              assert (Y===(B1^C1)) else $error("a211oi: !A1&!A2 -> Y should be B1^C1");
    if (pgood && (A1^A2))                 assert (Y===1'b0) else $error("a211oi: A1^A2 -> Y should be 0");
  end

  // Functional coverage (under power-good, known inputs)
  // Cover each producing minterm and key zero cases
  always_comb begin
    cover (pgood && inputs_known &&  A1 &&  A2 && Y);                      // term: A1&A2
    cover (pgood && inputs_known && !A1 && !A2 &&  B1 && !C1 && Y);        // term: !A1&!A2&B1&!C1
    cover (pgood && inputs_known && !A1 && !A2 && !B1 &&  C1 && Y);        // term: !A1&!A2&!B1&C1
    cover (pgood && inputs_known && (A1^A2)               && !Y);          // Y=0 when exactly one of A1,A2 is 1
    cover (pgood && inputs_known && !A1 && !A2 && !(B1^C1) && !Y);         // Y=0 when A1=A2=0 and B1==C1
  end

endmodule

// Bind into DUT
bind sky130_fd_sc_ls__a211oi sky130_fd_sc_ls__a211oi_sva a211oi_sva_i (.*);