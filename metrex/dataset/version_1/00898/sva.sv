// SVA checker for sky130_fd_sc_hs__dlymetal6s2s
module sky130_fd_sc_hs__dlymetal6s2s_chk
(
  input logic A, D, delay_VPWR, delay_VGND,
  input logic X,
  input logic delay_A, delay_D
);

  // delay_A/D set on source posedge in same timestep (post-NBA), and never fall
  property p_delay_A_sets_on_A_rise; @(posedge A) 1 |-> ##0 delay_A; endproperty
  assert property (p_delay_A_sets_on_A_rise);
  assert property (@(negedge delay_A) 0);
  assert property (@(posedge delay_A) A);

  property p_delay_D_sets_on_D_rise; @(posedge D) 1 |-> ##0 delay_D; endproperty
  assert property (p_delay_D_sets_on_D_rise);
  assert property (@(negedge delay_D) 0);
  assert property (@(posedge delay_D) D);

  // X is pure combinational function of delayed regs and rails (sampled post-NBA)
  property p_x_comb;
    @(posedge A or negedge A or
      posedge D or negedge D or
      posedge delay_VPWR or negedge delay_VPWR or
      posedge delay_VGND or negedge delay_VGND or
      posedge delay_A or negedge delay_A or
      posedge delay_D or negedge delay_D)
      ##0 (X == (delay_A && delay_VPWR && delay_VGND && delay_D));
  endproperty
  assert property (p_x_comb);

  // On rail drop, X must go low immediately
  assert property (@(negedge delay_VPWR) ##0 !X);
  assert property (@(negedge delay_VGND) ##0 !X);

  // X can only rise when all inputs to the AND are high
  assert property (@(posedge X) (delay_A && delay_D && delay_VPWR && delay_VGND));

  // Coverage
  cover property (@(posedge A) (delay_VPWR && delay_VGND && delay_D) ##0 X);
  cover property (@(posedge D) (delay_VPWR && delay_VGND && delay_A) ##0 X);
  cover property (@(posedge X) 1);
endmodule

// Bind into the DUT
bind sky130_fd_sc_hs__dlymetal6s2s sky130_fd_sc_hs__dlymetal6s2s_chk u_sva
(
  .A(A), .D(D), .delay_VPWR(delay_VPWR), .delay_VGND(delay_VGND),
  .X(X), .delay_A(delay_A), .delay_D(delay_D)
);