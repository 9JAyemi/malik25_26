// SVA for and_gate
module and_gate_sva (
  input logic Y,
  input logic A1, A2, A3, A4, B1,
  input logic VPWR, VPB, VGND, VNB
);

  // Core functional check (deferred to end of timestep to avoid races)
  always_comb begin
    assert #0 (Y === (A1 & A2 & A3 & A4 & B1))
      else $error("and_gate: Y != A1&A2&A3&A4&B1");

    // Controlling-0 on each input
    assert #0 (!(A1===1'b0) || (Y===1'b0));
    assert #0 (!(A2===1'b0) || (Y===1'b0));
    assert #0 (!(A3===1'b0) || (Y===1'b0));
    assert #0 (!(A4===1'b0) || (Y===1'b0));
    assert #0 (!(B1===1'b0) || (Y===1'b0));

    // Y==1 implies all inputs 1
    assert #0 (!(Y===1'b1) ||
               ((A1===1'b1)&&(A2===1'b1)&&(A3===1'b1)&&(A4===1'b1)&&(B1===1'b1)));

    // All inputs known => output known
    assert #0 (!$isunknown({A1,A2,A3,A4,B1}) || !$isunknown(Y));

    // If no zeros and any input X/Z => output must be X/Z
    assert #0 (((A1===1'b0)||(A2===1'b0)||(A3===1'b0)||(A4===1'b0)||(B1===1'b0)) ||
               (!$isunknown({A1,A2,A3,A4,B1})) ||
               $isunknown(Y));

    // Power pins validity
    assert #0 (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0);
  end

  // Coverage: 1) all ones -> Y=1
  //           2) single-zero controllability per pin -> Y=0
  //           3) X/Z propagation per pin with others 1
  always_comb begin
    cover (A1===1 && A2===1 && A3===1 && A4===1 && B1===1 && Y===1);

    cover (A1===0 && A2===1 && A3===1 && A4===1 && B1===1 && Y===0);
    cover (A1===1 && A2===0 && A3===1 && A4===1 && B1===1 && Y===0);
    cover (A1===1 && A2===1 && A3===0 && A4===1 && B1===1 && Y===0);
    cover (A1===1 && A2===1 && A3===1 && A4===0 && B1===1 && Y===0);
    cover (A1===1 && A2===1 && A3===1 && A4===1 && B1===0 && Y===0);

    cover ($isunknown(A1) && A2===1 && A3===1 && A4===1 && B1===1 && $isunknown(Y));
    cover (A1===1 && $isunknown(A2) && A3===1 && A4===1 && B1===1 && $isunknown(Y));
    cover (A1===1 && A2===1 && $isunknown(A3) && A4===1 && B1===1 && $isunknown(Y));
    cover (A1===1 && A2===1 && A3===1 && $isunknown(A4) && B1===1 && $isunknown(Y));
    cover (A1===1 && A2===1 && A3===1 && A4===1 && $isunknown(B1) && $isunknown(Y));
  end

endmodule

bind and_gate and_gate_sva sva (.*);