// SVA for my_logic
module my_logic_sva (
  input Y,
  input A1, A2, A3,
  input B1, C1,
  input VPWR, VGND, VPB, VNB
);

  // Power-good for checks
  wire pwr_good = (VPWR===1'b1) && (VPB===1'b1) && (VGND===1'b0) && (VNB===1'b0);

  // Core functional check (combinational, zero-delay)
  always_comb begin
    if (pwr_good) begin
      assert #0 (Y === ~(C1 & B1 & (A1 | A2 | A3)))
        else $error("my_logic: functional mismatch Y vs ~(C1 & B1 & (A1|A2|A3))");

      // Deterministic output cases (robust to Xs on non-controlling inputs)
      assert #0 ((B1!==1'b0) || (Y===1'b1))
        else $error("my_logic: B1=0 must force Y=1");
      assert #0 ((C1!==1'b0) || (Y===1'b1))
        else $error("my_logic: C1=0 must force Y=1");
      assert #0 (!((A1===1'b0)&&(A2===1'b0)&&(A3===1'b0)) || (Y===1'b1))
        else $error("my_logic: A1=A2=A3=0 must force Y=1");
      assert #0 (!((B1===1'b1)&&(C1===1'b1)&&((A1===1'b1)||(A2===1'b1)||(A3===1'b1))) || (Y===1'b0))
        else $error("my_logic: B1=C1=1 and any A=1 must force Y=0");

      // No X on Y when all data inputs are known
      if (!$isunknown({A1,A2,A3,B1,C1}))
        assert #0 (!$isunknown(Y))
          else $error("my_logic: Y is X with known inputs");
    end
  end

  // Functional coverage
  cover property (pwr_good && (Y===1'b0));
  cover property (pwr_good && (Y===1'b1));

  // Each Ai alone can drive Y low when B1=C1=1
  cover property (pwr_good && (B1===1'b1) && (C1===1'b1) &&
                  (A1===1'b1) && (A2===1'b0) && (A3===1'b0) && (Y===1'b0));
  cover property (pwr_good && (B1===1'b1) && (C1===1'b1) &&
                  (A1===1'b0) && (A2===1'b1) && (A3===1'b0) && (Y===1'b0));
  cover property (pwr_good && (B1===1'b1) && (C1===1'b1) &&
                  (A1===1'b0) && (A2===1'b0) && (A3===1'b1) && (Y===1'b0));

  // Distinct reasons for Y==1
  cover property (pwr_good && (B1===1'b0) && (Y===1'b1));
  cover property (pwr_good && (C1===1'b0) && (Y===1'b1));
  cover property (pwr_good && (A1===1'b0) && (A2===1'b0) && (A3===1'b0) &&
                  (B1===1'b1) && (C1===1'b1) && (Y===1'b1));

  // Y edges under valid power
  cover property (@(posedge Y) pwr_good);
  cover property (@(negedge Y) pwr_good);

endmodule

// Bind into DUT
bind my_logic my_logic_sva my_logic_sva_i (.*);