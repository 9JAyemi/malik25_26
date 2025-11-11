// Bind these SVA to the DUT
bind shift_reg shift_reg_sva #(
  .REG_SZ(REG_SZ),
  .FEED_FWD_IDX(FEED_FWD_IDX),
  .FEED_BKWD_IDX(FEED_BKWD_IDX)
) shift_reg_sva_b();

module shift_reg_sva #(
  parameter int REG_SZ = 93,
  parameter int FEED_FWD_IDX = 65,
  parameter int FEED_BKWD_IDX = 68
) ();

  // The following names are resolved in the bound instance scope:
  // clk_i, n_rst_i, ce_i, ld_i, ld_dat_i, dat_i, dat_o, z_o, dat_r, reg_in_s

  // Static parameter sanity
  initial begin
    assert (REG_SZ >= 81) else $error("REG_SZ must be >= 81");
    assert (FEED_FWD_IDX < REG_SZ) else $error("FEED_FWD_IDX out of range");
    assert (FEED_BKWD_IDX < REG_SZ) else $error("FEED_BKWD_IDX out of range");
  end

  default clocking cb @(posedge clk_i); endclocking
  default disable iff (!n_rst_i);

  // Reset behavior
  assert property (@cb !n_rst_i |-> dat_r == '0);
  assert property (@cb !n_rst_i |-> (z_o == 1'b0 && dat_o == 1'b0));

  // Combinational defines
  assert property (@cb reg_in_s == (dat_i ^ dat_r[FEED_BKWD_IDX]));
  assert property (@cb z_o == (dat_r[REG_SZ-1] ^ dat_r[FEED_FWD_IDX]));
  assert property (@cb dat_o == (z_o ^ (dat_r[REG_SZ-2] & dat_r[REG_SZ-3])));

  // Shift operation (CE has priority over LD)
  assert property (@cb ce_i |=> dat_r == { $past(dat_r[REG_SZ-2:0]),
                                           ($past(dat_i) ^ $past(dat_r[FEED_BKWD_IDX])) });

  // Hold when idle
  assert property (@cb (!ce_i && (ld_i == 3'b000)) |=> $stable(dat_r));

  // Loads (when ce_i==0): targeted slice updates, others hold; top region zeros (or top-3=111 if REG_SZ==111)
  // Common top region effect on any load
  if (REG_SZ == 111) begin
    assert property (@cb (!ce_i && (ld_i != 3'b000)) |=> (dat_r[110:108] == 3'b111 && dat_r[107:80] == '0));
  end else begin
    assert property (@cb (!ce_i && (ld_i != 3'b000)) |=> dat_r[REG_SZ-1:80] == '0);
  end

  // Load to [31:0] (priority over others)
  assert property (@cb (!ce_i && ld_i[0]) |=> (
                      dat_r[31:0]   == $past(ld_dat_i) &&
                      dat_r[63:32]  == $past(dat_r[63:32]) &&
                      dat_r[79:64]  == $past(dat_r[79:64])
                    ));

  // Load to [63:32] (only if ld_i[0]==0)
  assert property (@cb (!ce_i && !ld_i[0] && ld_i[1]) |=> (
                      dat_r[63:32]  == $past(ld_dat_i) &&
                      dat_r[31:0]   == $past(dat_r[31:0]) &&
                      dat_r[79:64]  == $past(dat_r[79:64])
                    ));

  // Load to [79:64] (only if ld_i[1:0]==0)
  assert property (@cb (!ce_i && !ld_i[0] && !ld_i[1] && ld_i[2]) |=> (
                      dat_r[79:64]  == $past(ld_dat_i[15:0]) &&
                      dat_r[63:32]  == $past(dat_r[63:32]) &&
                      dat_r[31:0]   == $past(dat_r[31:0])
                    ));

  // Coverage
  cover property (@cb ce_i && ((dat_i ^ dat_r[FEED_BKWD_IDX]) == 1'b0));
  cover property (@cb ce_i && ((dat_i ^ dat_r[FEED_BKWD_IDX]) == 1'b1));
  cover property (@cb (!ce_i && ld_i[0]));
  cover property (@cb (!ce_i && !ld_i[0] && ld_i[1]));
  cover property (@cb (!ce_i && !ld_i[0] && !ld_i[1] && ld_i[2]));
  cover property (@cb (ce_i && (ld_i != 3'b000))); // CE priority over load
  cover property (@cb z_o);
  cover property (@cb dat_o);
  if (REG_SZ == 111) cover property (@cb (!ce_i && (ld_i != 3'b000)) ##1 (dat_r[110:108] == 3'b111));

endmodule