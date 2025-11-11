// SVA for sky130_fd_sc_ls__a221oi (Y = ~((A1&A2) | (B1&B2) | C1))

module sky130_fd_sc_ls__a221oi_sva (
  input logic Y, A1, A2, B1, B2, C1,
  input logic and0_out, and1_out, nor0_out_Y
);

  // Functional equivalence (4-state exact)
  always_comb
    assert (Y === ~((A1 & A2) | (B1 & B2) | C1))
      else $error("a221oi: functional mismatch");

  // Structural net checks (catch internal wiring issues)
  always_comb begin
    assert (and0_out   === (B1 & B2))                 else $error("a221oi: and0_out mismatch");
    assert (and1_out   === (A1 & A2))                 else $error("a221oi: and1_out mismatch");
    assert (nor0_out_Y === ~(and0_out | C1 | and1_out)) else $error("a221oi: nor0_out_Y mismatch");
    assert (Y          === nor0_out_Y)                else $error("a221oi: buf mismatch");
  end

  // No-X on output when inputs are known
  always_comb
    if (!$isunknown({A1,A2,B1,B2,C1}))
      assert (!$isunknown(Y)) else $error("a221oi: Y unknown with known inputs");

  // Dominance checks (any asserted term forces Y=0)
  always_comb begin
    if (C1 === 1'b1)           assert (Y === 1'b0) else $error("a221oi: C1=1 must force Y=0");
    if ((A1 & A2) === 1'b1)    assert (Y === 1'b0) else $error("a221oi: A1&A2=1 must force Y=0");
    if ((B1 & B2) === 1'b1)    assert (Y === 1'b0) else $error("a221oi: B1&B2=1 must force Y=0");
  end

  // Coverage: both output values, each driving cause, and output toggles
  cover property (@(A1 or A2 or B1 or B2 or C1 or Y) (Y === 1'b1));
  cover property (@(A1 or A2 or B1 or B2 or C1 or Y) (Y === 1'b0));

  // Each single cause for Y=0
  cover property (@(A1 or A2 or B1 or B2 or C1 or Y)
                  (A1===1 && A2===1 && C1===0 && (B1===0 || B2===0)) && (Y===0));
  cover property (@(A1 or A2 or B1 or B2 or C1 or Y)
                  (B1===1 && B2===1 && C1===0 && (A1===0 || A2===0)) && (Y===0));
  cover property (@(A1 or A2 or B1 or B2 or C1 or Y)
                  (C1===1 && (A1===0 || A2===0) && (B1===0 || B2===0)) && (Y===0));

  // All-zero inputs -> Y=1
  cover property (@(A1 or A2 or B1 or B2 or C1 or Y)
                  (A1===0 && A2===0 && B1===0 && B2===0 && C1===0) && (Y===1));

  // Output transitions
  cover property (@(A1 or A2 or B1 or B2 or C1 or Y) $rose(Y));
  cover property (@(A1 or A2 or B1 or B2 or C1 or Y) $fell(Y));

endmodule

bind sky130_fd_sc_ls__a221oi
  sky130_fd_sc_ls__a221oi_sva sva (
    .Y(Y), .A1(A1), .A2(A2), .B1(B1), .B2(B2), .C1(C1),
    .and0_out(and0_out), .and1_out(and1_out), .nor0_out_Y(nor0_out_Y)
  );