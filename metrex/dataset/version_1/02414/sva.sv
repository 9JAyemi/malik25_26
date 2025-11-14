// SVA for hi_iso14443a
// Bind-friendly checker focused on protocol timing and outputs
module hi_iso14443a_sva (
  input  logic        pck0,
  input  logic        ck_1356meg,
  input  logic        ck_1356megb,
  input  logic        adc_clk,
  input  logic [7:0]  adc_d,
  input  logic        ssp_dout,
  input  logic        cross_hi,
  input  logic        cross_lo,
  input  logic [2:0]  mod_type,
  input  logic        ssp_clk,
  input  logic        ssp_frame,
  input  logic        ssp_din,
  input  logic        pwr_hi,
  input  logic        pwr_lo,
  input  logic        pwr_oe1,
  input  logic        pwr_oe2,
  input  logic        pwr_oe3,
  input  logic        pwr_oe4,
  input  logic        dbg
);

  // History window to make $past safe
  int hist_cnt;
  logic ok4, ok8, ok16, ok64, ok128;
  always @(negedge adc_clk) begin
    if (hist_cnt < 255) hist_cnt <= hist_cnt + 1;
  end
  assign ok4   = (hist_cnt >= 4);
  assign ok8   = (hist_cnt >= 8);
  assign ok16  = (hist_cnt >= 16);
  assign ok64  = (hist_cnt >= 64);
  assign ok128 = (hist_cnt >= 128);

  // 1) adc_clk must mirror ck_1356meg
  assert property (@(posedge ck_1356meg) adc_clk)
    else $error("adc_clk must be high on ck_1356meg posedge");
  assert property (@(negedge ck_1356meg) !adc_clk)
    else $error("adc_clk must be low on ck_1356meg negedge");

  // 2) Outputs never X/Z (sampled on adc_clk domain)
  assert property (@(negedge adc_clk)
    !$isunknown({ssp_clk, ssp_frame, ssp_din, pwr_hi, pwr_lo, pwr_oe1, pwr_oe2, pwr_oe3, pwr_oe4, dbg}))
    else $error("Outputs contain X/Z");

  // 3) ssp_clk period/duty (negedge adc_clk domain)
  // mod_type == 3'b000 => toggle every 4 negedges (period 8)
  assert property (@(negedge adc_clk) disable iff(!ok8)
    (mod_type==3'b000 && $past(mod_type,8)==3'b000)
      |-> (ssp_clk == ~$past(ssp_clk,4)) && (ssp_clk ==  $past(ssp_clk,8)))
    else $error("ssp_clk period violation for mod_type==000");
  assert property (@(negedge adc_clk) disable iff(!ok4)
    (mod_type==3'b000 && $past(mod_type,4)==3'b000 && $changed(ssp_clk)) |-> $stable(ssp_clk)[*3])
    else $error("ssp_clk must be stable for 3 cycles after change (mod_type==000)");

  // mod_type != 3'b000 => toggle every 8 negedges (period 16)
  assert property (@(negedge adc_clk) disable iff(!ok16)
    (mod_type!=3'b000 && $past(mod_type,16)!=3'b000)
      |-> (ssp_clk == ~$past(ssp_clk,8)) && (ssp_clk ==  $past(ssp_clk,16)))
    else $error("ssp_clk period violation for mod_type!=000");
  assert property (@(negedge adc_clk) disable iff(!ok8)
    (mod_type!=3'b000 && $past(mod_type,8)!=3'b000 && $changed(ssp_clk)) |-> $stable(ssp_clk)[*7])
    else $error("ssp_clk must be stable for 7 cycles after change (mod_type!=000)");

  // 4) ssp_clk/frame/din only change on negedge adc_clk
  assert property (@(posedge adc_clk) $stable(ssp_clk))
    else $error("ssp_clk changed outside negedge adc_clk");
  assert property (@(posedge adc_clk) $stable(ssp_frame))
    else $error("ssp_frame changed outside negedge adc_clk");
  assert property (@(posedge adc_clk) $stable(ssp_din))
    else $error("ssp_din changed outside negedge adc_clk");

  // 5) ssp_frame pulse width/period
  // mod_type == 3'b000: high 16 negedges, period 64
  assert property (@(negedge adc_clk) disable iff(!ok16)
    (mod_type==3'b000 && $past(mod_type,16)==3'b000 && $rose(ssp_frame))
      |-> ssp_frame[*16] ##1 !ssp_frame)
    else $error("ssp_frame width !=16 (mod_type==000)");
  assert property (@(negedge adc_clk) disable iff(!ok64)
    (mod_type==3'b000 && $past(mod_type,64)==3'b000 && $rose(ssp_frame))
      |=> !ssp_frame[*48] ##1 $rose(ssp_frame))
    else $error("ssp_frame period !=64 (mod_type==000)");

  // mod_type != 3'b000: high 16 negedges, period 128
  assert property (@(negedge adc_clk) disable iff(!ok16)
    (mod_type!=3'b000 && $past(mod_type,16)!=3'b000 && $rose(ssp_frame))
      |-> ssp_frame[*16] ##1 !ssp_frame)
    else $error("ssp_frame width !=16 (mod_type!=000)");
  assert property (@(negedge adc_clk) disable iff(!ok128)
    (mod_type!=3'b000 && $past(mod_type,128)!=3'b000 && $rose(ssp_frame))
      |=> !ssp_frame[*112] ##1 $rose(ssp_frame))
    else $error("ssp_frame period !=128 (mod_type!=000)");

  // 6) ssp_din stable at ssp_clk rising (setup/hold around sampling edge)
  assert property (@(negedge adc_clk) $rose(ssp_clk) |-> $stable(ssp_din))
    else $error("ssp_din not stable at ssp_clk rising");

  // 7) Power outputs
  // pwr_hi behavior
  assert property (@(posedge ck_1356megb or negedge ck_1356megb)
    (mod_type==3'b011) |-> (pwr_hi == ck_1356megb))
    else $error("pwr_hi must follow ck_1356megb when mod_type==011");
  assert property (@(posedge ck_1356megb or negedge ck_1356megb)
    (mod_type!=3'b011 && mod_type!=3'b100) |-> !pwr_hi)
    else $error("pwr_hi must be 0 for mod_type not in {011,100}");
  assert property (@(posedge ck_1356megb or negedge ck_1356megb)
    pwr_hi |-> ck_1356megb)
    else $error("pwr_hi cannot be 1 when ck_1356megb is 0");

  // pwr_oe4 only allowed in mod_type==010
  assert property (@(negedge adc_clk) (mod_type!=3'b010) |-> !pwr_oe4)
    else $error("pwr_oe4 asserted when mod_type!=010");

  // Constant-0 outputs
  assert property (@(negedge adc_clk) pwr_oe1==1'b0) else $error("pwr_oe1 must be 0");
  assert property (@(negedge adc_clk) pwr_oe2==1'b0) else $error("pwr_oe2 must be 0");
  assert property (@(negedge adc_clk) pwr_oe3==1'b0) else $error("pwr_oe3 must be 0");
  assert property (@(negedge adc_clk) pwr_lo ==1'b0) else $error("pwr_lo must be 0");

  // 8) dbg should be a clean divide-by-16 of negedge adc_clk (toggle every 8 negedges)
  assert property (@(negedge adc_clk) disable iff(!ok16)
    (dbg == ~$past(dbg,8)) && (dbg == $past(dbg,16)))
    else $error("dbg divide ratio incorrect");

  // Coverage
  cover property (@(negedge adc_clk) mod_type==3'b000);
  cover property (@(negedge adc_clk) mod_type==3'b010);
  cover property (@(negedge adc_clk) mod_type==3'b011);
  cover property (@(negedge adc_clk) mod_type==3'b100);

  cover property (@(negedge adc_clk) $rose(ssp_frame) && mod_type==3'b000);
  cover property (@(negedge adc_clk) $rose(ssp_frame) && mod_type!=3'b000);

  cover property (@(negedge adc_clk) mod_type==3'b010 && pwr_oe4);
  cover property (@(posedge ck_1356megb) mod_type==3'b011 && ck_1356megb && pwr_hi);
  cover property (@(negedge adc_clk) $rose(ssp_clk));
  cover property (@(negedge adc_clk) $changed(ssp_din));

endmodule

// Bind into DUT (connect only top-level ports)
bind hi_iso14443a hi_iso14443a_sva u_hi_iso14443a_sva (
  .pck0        (pck0),
  .ck_1356meg  (ck_1356meg),
  .ck_1356megb (ck_1356megb),
  .adc_clk     (adc_clk),
  .adc_d       (adc_d),
  .ssp_dout    (ssp_dout),
  .cross_hi    (cross_hi),
  .cross_lo    (cross_lo),
  .mod_type    (mod_type),
  .ssp_clk     (ssp_clk),
  .ssp_frame   (ssp_frame),
  .ssp_din     (ssp_din),
  .pwr_hi      (pwr_hi),
  .pwr_lo      (pwr_lo),
  .pwr_oe1     (pwr_oe1),
  .pwr_oe2     (pwr_oe2),
  .pwr_oe3     (pwr_oe3),
  .pwr_oe4     (pwr_oe4),
  .dbg         (dbg)
);