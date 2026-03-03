// SVA checker for sky130_fd_sc_ms__a31oi
// Function: Y = ~ (B1 | (A1 & A2 & A3))

module sky130_fd_sc_ms__a31oi_sva (
  input logic A1, A2, A3, B1,
  input logic Y
);

  // Functional equivalence (4-state aware); zero-delay to avoid races
  always_comb
    assert #0 (Y === ~(B1 | (A1 & A2 & A3)))
      else $error("a31oi func mismatch: Y=%b A1=%b A2=%b A3=%b B1=%b", Y,A1,A2,A3,B1);

  // Truth-table coverage (all 16 input combinations), with expected Y
  // B1 = 1 -> Y = 0 for all A's
  cover property (@(A1 or A2 or A3 or B1) (B1==1 && A1==0 && A2==0 && A3==0 && Y==0));
  cover property (@(A1 or A2 or A3 or B1) (B1==1 && A1==0 && A2==0 && A3==1 && Y==0));
  cover property (@(A1 or A2 or A3 or B1) (B1==1 && A1==0 && A2==1 && A3==0 && Y==0));
  cover property (@(A1 or A2 or A3 or B1) (B1==1 && A1==0 && A2==1 && A3==1 && Y==0));
  cover property (@(A1 or A2 or A3 or B1) (B1==1 && A1==1 && A2==0 && A3==0 && Y==0));
  cover property (@(A1 or A2 or A3 or B1) (B1==1 && A1==1 && A2==0 && A3==1 && Y==0));
  cover property (@(A1 or A2 or A3 or B1) (B1==1 && A1==1 && A2==1 && A3==0 && Y==0));
  cover property (@(A1 or A2 or A3 or B1) (B1==1 && A1==1 && A2==1 && A3==1 && Y==0));

  // B1 = 0 -> Y = ~(A1&A2&A3)
  cover property (@(A1 or A2 or A3 or B1) (B1==0 && A1==0 && A2==0 && A3==0 && Y==1));
  cover property (@(A1 or A2 or A3 or B1) (B1==0 && A1==0 && A2==0 && A3==1 && Y==1));
  cover property (@(A1 or A2 or A3 or B1) (B1==0 && A1==0 && A2==1 && A3==0 && Y==1));
  cover property (@(A1 or A2 or A3 or B1) (B1==0 && A1==0 && A2==1 && A3==1 && Y==1));
  cover property (@(A1 or A2 or A3 or B1) (B1==0 && A1==1 && A2==0 && A3==0 && Y==1));
  cover property (@(A1 or A2 or A3 or B1) (B1==0 && A1==1 && A2==0 && A3==1 && Y==1));
  cover property (@(A1 or A2 or A3 or B1) (B1==0 && A1==1 && A2==1 && A3==0 && Y==1));
  cover property (@(A1 or A2 or A3 or B1) (B1==0 && A1==1 && A2==1 && A3==1 && Y==0));

  // X-prop corner coverage (useful to see masked and propagated X behavior)
  cover property (@(A1 or A2 or A3 or B1) (B1===1 && (|$isunknown({A1,A2,A3})) && Y===0));
  cover property (@(A1 or A2 or A3 or B1)
                  (B1===0 && (A1!==0 && A2!==0 && A3!==0) && !(A1===1 && A2===1 && A3===1) && $isunknown(Y)));

endmodule

// Bind into DUT
bind sky130_fd_sc_ms__a31oi sky130_fd_sc_ms__a31oi_sva sva_i (.A1(A1), .A2(A2), .A3(A3), .B1(B1), .Y(Y));