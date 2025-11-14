// SVA for sky130_fd_sc_lp__or4bb
module sky130_fd_sc_lp__or4bb_sva (
  input logic A, B, C_N, D_N, X
);
  // Functional equivalence (4-state exact)
  property p_func; X === (A | B | ~C_N | ~D_N); endproperty
  assert property (@(A or B or C_N or D_N or X) p_func)
    else $error("sky130_fd_sc_lp__or4bb: functional mismatch");

  // Dominating inputs drive X high
  assert property (@(A or B or C_N or D_N) (A===1) |-> ##0 (X===1));
  assert property (@(A or B or C_N or D_N) (B===1) |-> ##0 (X===1));
  assert property (@(A or B or C_N or D_N) (C_N===0) |-> ##0 (X===1));
  assert property (@(A or B or C_N or D_N) (D_N===0) |-> ##0 (X===1));

  // Only-low condition and consistency both ways
  assert property (@(A or B or C_N or D_N)
                   ((A===0)&&(B===0)&&(C_N===1)&&(D_N===1)) |-> ##0 (X===0));
  assert property (@(A or B or C_N or D_N)
                   (X===0) |-> ##0 ((A===0)&&(B===0)&&(C_N===1)&&(D_N===1)));
  assert property (@(A or B or C_N or D_N)
                   (X===1) |-> ##0 ((A===1)||(B===1)||(C_N===0)||(D_N===0)));

  // No unknown on output when inputs are all known
  assert property (@(A or B or C_N or D_N)
                   (!$isunknown({A,B,C_N,D_N})) |-> ##0 !$isunknown(X));

  // Coverage: X activity and both polarities
  cover property (@(A or B or C_N or D_N) $changed(X));
  cover property (@(A or B or C_N or D_N) (X===0));
  cover property (@(A or B or C_N or D_N) (X===1));

  // Coverage: all 16 input combinations (with known inputs)
  for (genvar i=0; i<16; i++) begin : gen_tt_cov
    localparam logic [3:0] PAT = i[3:0];
    cover property (@(A or B or C_N or D_N)
                    (!$isunknown({A,B,C_N,D_N}) && {A,B,C_N,D_N} == PAT));
  end
endmodule

bind sky130_fd_sc_lp__or4bb sky130_fd_sc_lp__or4bb_sva u_or4bb_sva (
  .A(A), .B(B), .C_N(C_N), .D_N(D_N), .X(X)
);