// SVA checker for eg_limiter
// Focused, combinational, bindable; uses immediate assertions and covers
// to avoid dependence on a clock.

`ifndef SYNTHESIS
module eg_limiter_sva (
  input  logic [6:0] lfo_mod,
  input  logic       amsen,
  input  logic [1:0] ams,
  input  logic [6:0] tl,
  input  logic [9:0] eg_pure_in,
  input  logic       ssg_inv,
  input  logic [9:0] eg_limited,

  // internal DUT regs (bound hierarchically)
  input  logic [5:0]  am_inverted,
  input  logic [8:0]  am_final,
  input  logic [9:0]  eg_pream,
  input  logic [11:0] sum_eg_tl,
  input  logic [11:0] sum_eg_tl_am
);

  // Golden (reference) combinational calculations
  logic [5:0]  am_inverted_g;
  logic [8:0]  am_final_g;
  logic [9:0]  eg_pream_g;
  logic [11:0] sum_eg_tl_g;
  logic [11:0] sum_eg_tl_am_g;
  logic [9:0]  eg_limited_g;

  always_comb begin
    am_inverted_g = lfo_mod[6] ? ~lfo_mod[5:0] : lfo_mod[5:0];

    am_final_g =
      amsen
        ? (ams == 2'b01) ? {5'd0, am_inverted_g[5:2]} :
          (ams == 2'b10) ? {3'd0, am_inverted_g}      :
          (ams == 2'b11) ? {2'd0, am_inverted_g, 1'b0} :
                           9'd0
        : 9'd0;

    eg_pream_g = ssg_inv ? (10'h200 - eg_pure_in) : eg_pure_in;

    // match DUT widths exactly
    sum_eg_tl_g    = {1'b0, tl, 3'b000} + {1'b0, eg_pream_g};
    sum_eg_tl_am_g = sum_eg_tl_g + {3'd0, am_final_g};

    eg_limited_g = (sum_eg_tl_am_g[11:10] == 2'b00) ? sum_eg_tl_am_g[9:0] : 10'h3FF;
  end

  // Sanity: no X/Z on inputs/outputs/internals
  always_comb begin
    assert (!$isunknown({lfo_mod, amsen, ams, tl, eg_pure_in, ssg_inv}))
      else $error("eg_limiter inputs contain X/Z");

    assert (!$isunknown({am_inverted, am_final, eg_pream, sum_eg_tl, sum_eg_tl_am, eg_limited}))
      else $error("eg_limiter internal/output contains X/Z");
  end

  // Equivalence checks against golden model
  always_comb begin
    assert (am_inverted == am_inverted_g)
      else $error("am_inverted mismatch: got %0h exp %0h", am_inverted, am_inverted_g);

    assert (am_final == am_final_g)
      else $error("am_final mismatch: got %0h exp %0h", am_final, am_final_g);

    assert (eg_pream == eg_pream_g)
      else $error("eg_pream mismatch: got %0h exp %0h", eg_pream, eg_pream_g);

    assert (sum_eg_tl == sum_eg_tl_g)
      else $error("sum_eg_tl mismatch: got %0h exp %0h", sum_eg_tl, sum_eg_tl_g);

    assert (sum_eg_tl_am == sum_eg_tl_am_g)
      else $error("sum_eg_tl_am mismatch: got %0h exp %0h", sum_eg_tl_am, sum_eg_tl_am_g);

    assert (eg_limited == eg_limited_g)
      else $error("eg_limited mismatch: got %0h exp %0h", eg_limited, eg_limited_g);
  end

  // Range/consistency checks
  always_comb begin
    // sum_eg_tl fits in 11 bits by design
    assert (sum_eg_tl <= 12'd2047) else $error("sum_eg_tl out of range");

    // High bits vs threshold are consistent
    assert ((sum_eg_tl_am <= 12'd1023) == (sum_eg_tl_am[11:10] == 2'b00))
      else $error("sum_eg_tl_am[11:10] inconsistent with magnitude");

    // Output is saturated to 10 bits
    assert (eg_limited <= 10'h3FF) else $error("eg_limited exceeds 10-bit max");
  end

  // Functional covers (immediate), to ensure all modes/paths exercise
  always_comb begin
    // AM mode selections
    cover ({amsen,ams} == 3'b1_01);
    cover ({amsen,ams} == 3'b1_10);
    cover ({amsen,ams} == 3'b1_11);
    cover ({amsen,ams} == 3'b1_00);
    cover (!amsen);

    // LFO polarity handling
    cover (lfo_mod[6] == 1'b0);
    cover (lfo_mod[6] == 1'b1);

    // SSG inversion path
    cover (ssg_inv == 1'b0);
    cover (ssg_inv == 1'b1);

    // Saturation boundary and both outcomes
    cover (sum_eg_tl_am == 12'd1023);   // exact boundary
    cover (sum_eg_tl_am == 12'd1024);   // just over boundary (forces clamp)
    cover (eg_limited == 10'h3FF);      // saturated
    cover (eg_limited == sum_eg_tl_am[9:0]); // pass-through
  end

endmodule

// Bind to DUT; hierarchical connects pull in internals
bind eg_limiter eg_limiter_sva eg_limiter_sva_i (
  .lfo_mod(lfo_mod),
  .amsen(amsen),
  .ams(ams),
  .tl(tl),
  .eg_pure_in(eg_pure_in),
  .ssg_inv(ssg_inv),
  .eg_limited(eg_limited),

  .am_inverted(am_inverted),
  .am_final(am_final),
  .eg_pream(eg_pream),
  .sum_eg_tl(sum_eg_tl),
  .sum_eg_tl_am(sum_eg_tl_am)
);
`endif