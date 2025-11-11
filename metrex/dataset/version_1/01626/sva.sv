// SVA for fpu_denorm_3to1
// Bind-only monitor; no DUT changes.

module fpu_denorm_3to1_sva (
  input logic din2_din1_nz_hi,
  input logic din2_din1_denorm_hi,
  input logic din2_din1_nz_mid,
  input logic din2_din1_denorm_mid,
  input logic din2_din1_nz_lo,
  input logic din2_din1_denorm_lo,
  input logic din2_din1_nz,
  input logic din2_din1_denorm
);

  // Sample on any input/output change
  event ev; always @* -> ev;

  // Functional equivalence (core spec)
  property p_nz_def;
    @(ev) din2_din1_nz == (din2_din1_nz_hi || din2_din1_nz_mid || din2_din1_nz_lo);
  endproperty
  a_nz_def: assert property (p_nz_def);

  property p_denorm_def;
    @(ev) din2_din1_denorm ==
      ((din2_din1_nz_hi && din2_din1_denorm_hi) ||
       (!din2_din1_nz_hi && din2_din1_nz_mid && din2_din1_denorm_mid) ||
       (!din2_din1_nz_hi && !din2_din1_nz_mid && din2_din1_denorm_lo));
  endproperty
  a_denorm_def: assert property (p_denorm_def);

  // X-prop guard: known inputs imply known outputs
  property p_no_x;
    @(ev) !$isunknown({din2_din1_nz_hi,
                       din2_din1_denorm_hi,
                       din2_din1_nz_mid,
                       din2_din1_denorm_mid,
                       din2_din1_nz_lo,
                       din2_din1_denorm_lo})
          |-> !$isunknown({din2_din1_nz, din2_din1_denorm});
  endproperty
  a_no_x: assert property (p_no_x);

  // Coverage: exercise all priority paths and output polarities
  c_nz0:       cover property (@(ev) din2_din1_nz == 1'b0);
  c_nz1:       cover property (@(ev) din2_din1_nz == 1'b1);
  c_denorm0:   cover property (@(ev) din2_din1_denorm == 1'b0);
  c_denorm1:   cover property (@(ev) din2_din1_denorm == 1'b1);

  c_hi_path:   cover property (@(ev)  din2_din1_nz_hi
                                    && (din2_din1_denorm == din2_din1_denorm_hi));
  c_mid_path:  cover property (@(ev) !din2_din1_nz_hi && din2_din1_nz_mid
                                    && (din2_din1_denorm == din2_din1_denorm_mid));
  c_lo_path:   cover property (@(ev) !din2_din1_nz_hi && !din2_din1_nz_mid
                                    && (din2_din1_denorm == din2_din1_denorm_lo));

endmodule

bind fpu_denorm_3to1 fpu_denorm_3to1_sva
(
  .din2_din1_nz_hi     (din2_din1_nz_hi),
  .din2_din1_denorm_hi (din2_din1_denorm_hi),
  .din2_din1_nz_mid    (din2_din1_nz_mid),
  .din2_din1_denorm_mid(din2_din1_denorm_mid),
  .din2_din1_nz_lo     (din2_din1_nz_lo),
  .din2_din1_denorm_lo (din2_din1_denorm_lo),
  .din2_din1_nz        (din2_din1_nz),
  .din2_din1_denorm    (din2_din1_denorm)
);