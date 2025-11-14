// SVA for sky130_fd_sc_lp__a2bb2oi and sky130_fd_sc_lp__a2bb2oi_lp

module a2bb2oi_sva (
  input logic Y,
  input logic A1_N,
  input logic A2_N,
  input logic B1,
  input logic B2
);

  // Functional equivalence (delta-cycle settle)
  property p_func;
    @(A1_N or A2_N or B1 or B2) ##0
      (Y === ((A1_N & B1) | (A2_N & B2)));
  endproperty
  a_func: assert property (p_func);

  // If all inputs are known, output must be known (no X/Z leakage)
  property p_known_out;
    @(A1_N or A2_N or B1 or B2)
      (!$isunknown({A1_N,A2_N,B1,B2})) |-> ##0 !$isunknown(Y);
  endproperty
  a_known_out: assert property (p_known_out);

  // Minimal but complete functional coverage
  c_only_leg1: cover property (@(A1_N or A2_N or B1 or B2) ##0
                    (A1_N & B1) && !(A2_N & B2) && (Y==1));
  c_only_leg2: cover property (@(A1_N or A2_N or B1 or B2) ##0
                    (A2_N & B2) && !(A1_N & B1) && (Y==1));
  c_both_legs: cover property (@(A1_N or A2_N or B1 or B2) ##0
                    (A1_N & B1) && (A2_N & B2) && (Y==1));
  c_neither:   cover property (@(A1_N or A2_N or B1 or B2) ##0
                    !(A1_N & B1) && !(A2_N & B2) && (Y==0));

  // X-propagation coverage
  c_xprop: cover property (@(A1_N or A2_N or B1 or B2) ##0
                    $isunknown({A1_N,A2_N,B1,B2}) && $isunknown(Y));

endmodule

// Bind to both implementations
bind sky130_fd_sc_lp__a2bb2oi    a2bb2oi_sva u_a2bb2oi_sva (.*);
bind sky130_fd_sc_lp__a2bb2oi_lp a2bb2oi_sva u_a2bb2oi_lp_sva (.*);