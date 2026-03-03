// SVA for sky130_fd_sc_ls__a2bb2oi
module sky130_fd_sc_ls__a2bb2oi_sva (
  input logic A1_N, A2_N, B1, B2, Y
);

  `define ANY_EDGE (posedge A1_N or negedge A1_N or \
                     posedge A2_N or negedge A2_N or \
                     posedge B1   or negedge B1   or \
                     posedge B2   or negedge B2)

  // Local terms
  logic tA, tB;
  always_comb begin
    tA = (~A1_N & ~A2_N);
    tB = (B1 & B2);
  end

  // Functional equivalence (use ##0 to avoid preponed sampling race)
  property p_eq; @(`ANY_EDGE) ##0 (Y === ~(tA | tB)); endproperty
  assert property (p_eq);

  // No X on Y when inputs are known
  property p_no_x; @(`ANY_EDGE) (!$isunknown({A1_N,A2_N,B1,B2})) |-> ##0 (!$isunknown(Y)); endproperty
  assert property (p_no_x);

  // Dominance checks
  property p_tA_dominates; @(`ANY_EDGE) tA |-> ##0 (Y == 1'b0); endproperty
  assert property (p_tA_dominates);

  property p_tB_dominates; @(`ANY_EDGE) tB |-> ##0 (Y == 1'b0); endproperty
  assert property (p_tB_dominates);

  // Y high only when both terms are 0
  property p_Y_high_conditions; @(`ANY_EDGE) Y |-> ##0 (!tA && !tB); endproperty
  assert property (p_Y_high_conditions);

  // Compact functional coverage of all cause combinations and Y activity
  cover property (@(`ANY_EDGE) ##0 (!tA && !tB &&  Y)); // both 0 -> Y=1
  cover property (@(`ANY_EDGE) ##0 ( tA && !tB && !Y)); // tA=1
  cover property (@(`ANY_EDGE) ##0 (!tA &&  tB && !Y)); // tB=1
  cover property (@(`ANY_EDGE) ##0 ( tA &&  tB && !Y)); // both 1
  cover property (@(`ANY_EDGE) ##0 $changed(Y));

endmodule

bind sky130_fd_sc_ls__a2bb2oi sky130_fd_sc_ls__a2bb2oi_sva sva_i (
  .A1_N(A1_N), .A2_N(A2_N), .B1(B1), .B2(B2), .Y(Y)
);