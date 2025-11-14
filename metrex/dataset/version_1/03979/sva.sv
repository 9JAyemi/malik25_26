// SVA checker for sky130_fd_sc_lp__a22oi
module sky130_fd_sc_lp__a22oi_sva (
  input logic Y,
  input logic A1,
  input logic A2,
  input logic B1,
  input logic B2
);

  // Sample on any input edge
  default clocking cb @(
      posedge A1 or negedge A1 or
      posedge A2 or negedge A2 or
      posedge B1 or negedge B1 or
      posedge B2 or negedge B2
  ); endclocking

  // Functional equivalence (delta-stable)
  ap_func_eq: assert property (##0 (Y === ~((A1 & A2) | (B1 & B2))));

  // Key implications
  ap_Apair_forces_low: assert property (##0 ((A1 & A2) |-> !Y));
  ap_Bpair_forces_low: assert property (##0 ((B1 & B2) |-> !Y));
  ap_high_implies_no_pairs: assert property (##0 (Y |-> (!(A1 & A2) && !(B1 & B2))));

  // No unknown on Y when inputs are known
  ap_no_x_on_y: assert property (##0 (!$isunknown({A1,A2,B1,B2}) |-> !$isunknown(Y)));

  // Basic output coverage
  cp_y0: cover property (##0 (!Y));
  cp_y1: cover property (##0 ( Y));

  // Full input combination coverage with expected Y
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : gen_cov
      // Cover each known 4-bit input combination and correct Y
      cover property (##0 ( {A1,A2,B1,B2} == i[3:0] &&
                            (Y == ~((i[3]&i[2]) | (i[1]&i[0]))) ));
    end
  endgenerate

endmodule

// Bind to the DUT
bind sky130_fd_sc_lp__a22oi sky130_fd_sc_lp__a22oi_sva u_sva (
  .Y(Y), .A1(A1), .A2(A2), .B1(B1), .B2(B2)
);