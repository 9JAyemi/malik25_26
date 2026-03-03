// SVA for and2b: X = ~A_N & B, with power/well checks and concise coverage
module and2b_sva (
  input  logic A_N,
  input  logic B,
  input  logic X,
  input  logic VPB,
  input  logic VPWR,
  input  logic VGND,
  input  logic VNB
);

  // Power/well must be valid and static
  ap_pwr_static: assert property (@(VPWR or VGND or VPB or VNB)
                                  VPWR === 1'b1 && VGND === 1'b0 &&
                                  VPB  === 1'b1 && VNB  === 1'b0)
    else $error("and2b: Power/well pins invalid or changed");

  // Define power-good gating for functional checks/coverage
  logic pwr_good;
  assign pwr_good = (VPWR === 1'b1) && (VGND === 1'b0) &&
                    (VPB  === 1'b1) && (VNB  === 1'b0);

  default disable iff (!pwr_good)

  // Functional equivalence (combinational, 4-state accurate)
  // Fires on any combinational change
  always_comb
    ap_func_eq: assert (X === ((~A_N) & B))
      else $error("and2b: X != (~A_N & B)  A_N=%b B=%b X=%b", A_N, B, X);

  // When both inputs are known under good power, output must be known
  ap_known_out: assert property (@(A_N or B or X) !$isunknown({A_N,B}) |-> !$isunknown(X))
    else $error("and2b: X unknown while inputs known  A_N=%b B=%b X=%b", A_N, B, X);

  // Useful one-cycle implications (same-cycle) for key corners
  ap_b0_forces_0:  assert property (@(A_N or B or X) (B  === 1'b0) |-> (X === 1'b0));
  ap_an1_forces_0: assert property (@(A_N or B or X) (A_N=== 1'b1) |-> (X === 1'b0));
  ap_hit_1:        assert property (@(A_N or B or X) (A_N=== 1'b0 && B===1'b1) |-> (X === 1'b1));

  // Coverage: power-good observed
  cp_pwr_good:     cover property (@(posedge pwr_good) pwr_good);

  // Coverage: all input combos under good power
  cp_in_00:        cover property (@(A_N or B) pwr_good && (A_N===1'b0) && (B===1'b0));
  cp_in_01:        cover property (@(A_N or B) pwr_good && (A_N===1'b0) && (B===1'b1));
  cp_in_10:        cover property (@(A_N or B) pwr_good && (A_N===1'b1) && (B===1'b0));
  cp_in_11:        cover property (@(A_N or B) pwr_good && (A_N===1'b1) && (B===1'b1));

  // Coverage: observe X=1 and X=0 under good power
  cp_x1:           cover property (@(A_N or B or X) pwr_good && X===1'b1);
  cp_x0:           cover property (@(A_N or B or X) pwr_good && X===1'b0);

  // Coverage: specific zero-by-each-controlling-input scenarios
  cp_x0_by_b0:     cover property (@(A_N or B or X) pwr_good && (B===1'b0) && (X===1'b0));
  cp_x0_by_an1:    cover property (@(A_N or B or X) pwr_good && (A_N===1'b1) && (X===1'b0));

endmodule

// Bind to DUT
bind and2b and2b_sva u_and2b_sva (.*);