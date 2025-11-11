// SVA for sky130_fd_sc_lp__a2bb2oi
// Function: Y = (A1_N | A2_N) & (~B1 | ~B2)

module sky130_fd_sc_lp__a2bb2oi_sva;

  // Functional equivalence (x-tolerant and known-only versions)
  assert property (@(*) ##0 (Y === ((A1_N | A2_N) & (~B1 | ~B2))));
  assert property (@(*) (!$isunknown({A1_N,A2_N,B1,B2})) |-> ##0 (Y == ((A1_N | A2_N) & (~B1 | ~B2))));

  // Structural consistency of internal nets
  assert property (@(*) ##0 (and0_out   === (B1 & B2)));
  assert property (@(*) ##0 (nor0_out   === ~(A1_N | A2_N)));
  assert property (@(*) ##0 (nor1_out_Y === ~(nor0_out | and0_out)));
  assert property (@(*) ##0 (Y          === nor1_out_Y));

  // Dominance/short-circuit properties
  assert property (@(*) (B1===1 && B2===1)                 |-> ##0 (Y===0));
  assert property (@(*) (A1_N===0 && A2_N===0)             |-> ##0 (Y===0));
  assert property (@(*) (B1===0 || B2===0)                 |-> ##0 (Y === (A1_N | A2_N)));
  assert property (@(*) ((A1_N===1 || A2_N===1) && (B1===0 || B2===0)) |-> ##0 (Y===1));

  // X-safety
  assert property (@(*) (!$isunknown({A1_N,A2_N,B1,B2})) |-> ##0 (!$isunknown(Y)));

  // Coverage (key modes, internal terms, and output activity)
  cover property (@(*) ##0 (Y==1));
  cover property (@(*) ##0 (Y==0));
  cover property (@(*) ##0 (B1 && B2));                      // and0_out==1
  cover property (@(*) ##0 (~A1_N && ~A2_N));                // nor0_out==1
  cover property (@(*) ##0 (A1_N && (B1==0 || B2==0)));      // A1_N term enables Y
  cover property (@(*) ##0 (A2_N && (B1==0 || B2==0)));      // A2_N term enables Y
  cover property (@(*) $rose(Y));
  cover property (@(*) $fell(Y));
  cover property (@(*) $isunknown(Y));

endmodule

bind sky130_fd_sc_lp__a2bb2oi sky130_fd_sc_lp__a2bb2oi_sva sva_i();