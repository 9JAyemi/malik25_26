// SVA for mult_gate: checks functionality, X-handling, and covers key cases.
module mult_gate_sva;
  default clocking cb @(*); endclocking

  // Internal AND terms must match their inputs when inputs are known
  ap_w1: assert property (!$isunknown({A,B,C}) |-> (! $isunknown(w1) && (w1 == (C & B & A))));
  ap_w2: assert property (!$isunknown({D,E,F}) |-> (! $isunknown(w2) && (w2 == (F & E & D))));
  ap_w3: assert property (!$isunknown({G,H,I}) |-> (! $isunknown(w3) && (w3 == (I & H & G))));

  // Output OR function must match when all inputs are known
  ap_y_func: assert property
    (!$isunknown({A,B,C,D,E,F,G,H,I,J})
      |-> (! $isunknown(Y) && (Y == ((I & H & G) | (F & E & D) | (C & B & A) | J))));

  // J high must force Y high even if others are X
  ap_j_dominates: assert property ((J === 1'b1) |-> (Y === 1'b1));

  // If Y is low with known inputs, all terms and J must be 0
  ap_y_low_backward: assert property
    ((!$isunknown({A,B,C,D,E,F,G,H,I,J}) && (Y == 1'b0))
      |-> (!(I & H & G) && !(F & E & D) && !(C & B & A) && (J == 1'b0)));

  // Coverage: each source alone, overlaps, all-zero, and Y toggles
  cp_j_only:      cover property (!$isunknown({A,B,C,D,E,F,G,H,I,J}) && J && !(I & H & G) && !(F & E & D) && !(C & B & A) && Y);
  cp_w1_only:     cover property (!$isunknown({A,B,C,D,E,F,G,H,I,J}) && !J && (C & B & A) && !(F & E & D) && !(I & H & G) && Y);
  cp_w2_only:     cover property (!$isunknown({A,B,C,D,E,F,G,H,I,J}) && !J && (F & E & D) && !(C & B & A) && !(I & H & G) && Y);
  cp_w3_only:     cover property (!$isunknown({A,B,C,D,E,F,G,H,I,J}) && !J && (I & H & G) && !(C & B & A) && !(F & E & D) && Y);
  cp_all_zero:    cover property (!$isunknown({A,B,C,D,E,F,G,H,I,J}) && !J && !(I & H & G) && !(F & E & D) && !(C & B & A) && !Y);
  cp_overlap_12:  cover property (!$isunknown({A,B,C,D,E,F,G,H,I,J}) && !J && (C & B & A) && (F & E & D) && !(I & H & G) && Y);
  cp_overlap_23:  cover property (!$isunknown({A,B,C,D,E,F,G,H,I,J}) && !J && (F & E & D) && (I & H & G) && !(C & B & A) && Y);
  cp_overlap_13:  cover property (!$isunknown({A,B,C,D,E,F,G,H,I,J}) && !J && (C & B & A) && (I & H & G) && !(F & E & D) && Y);
  cp_three_terms: cover property (!$isunknown({A,B,C,D,E,F,G,H,I,J}) && !J && (C & B & A) && (F & E & D) && (I & H & G) && Y);

  cp_y_rise: cover property ($rose(Y));
  cp_y_fall: cover property ($fell(Y));
endmodule

bind mult_gate mult_gate_sva sva_inst();