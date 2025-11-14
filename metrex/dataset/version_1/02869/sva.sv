// SVA for hpdmc_busif
// Bind into the DUT scope so we can see internals like mgmt_stb_en.

module hpdmc_busif_sva #(parameter int sdram_depth = 23) ();

  // Static sanity
  initial begin
    assert (sdram_depth >= 2)
      else $error("hpdmc_busif: sdram_depth must be >=2 (got %0d)", sdram_depth);
  end

  // Default clock
  default clocking cb @(posedge sys_clk); endclocking

  // Combinational mappings
  assert property (mgmt_we      == fml_we);
  assert property (mgmt_address == fml_adr[sdram_depth-1:1]);
  assert property (mgmt_stb     == (fml_stb & mgmt_stb_en));
  assert property (fml_ack      == data_ack);

  // mgmt_stb_en next-state behavior
  // Reset forces enable
  assert property (sdram_rst |-> mgmt_stb_en);

  // data_ack dominates (sets enable)
  assert property (!sdram_rst && data_ack |-> mgmt_stb_en);

  // mgmt_ack alone clears enable
  assert property (!sdram_rst && mgmt_ack && !data_ack |-> !mgmt_stb_en);

  // Hold when no event (exclude cycles around reset for $past safety)
  assert property (!sdram_rst && !$past(sdram_rst) && !mgmt_ack && !data_ack
                   |-> mgmt_stb_en == $past(mgmt_stb_en));

  // Basic X-protection on outputs when out of reset (optional but useful)
  assert property (!sdram_rst |-> !$isunknown({mgmt_stb, mgmt_we, mgmt_address, fml_ack}));

  // ----------------------------------
  // Coverage
  // ----------------------------------

  // Reset observed driving enable high
  cover property (sdram_rst && mgmt_stb_en);

  // Disable via mgmt_ack then re-enable via data_ack
  cover property (!sdram_rst ##1 mgmt_stb_en && mgmt_ack && !data_ack
                  ##1 !mgmt_stb_en
                  ##1 data_ack
                  ##1 mgmt_stb_en);

  // Both mgmt_ack and data_ack same cycle => enable remains/sets high
  cover property (!sdram_rst && mgmt_ack && data_ack && mgmt_stb_en);

  // Gating: blocked strobe
  cover property (!sdram_rst && fml_stb && !mgmt_stb_en && !mgmt_stb);

  // Gating: passed strobe
  cover property (!sdram_rst && fml_stb &&  mgmt_stb_en &&  mgmt_stb);

  // Address slice invariance to LSB toggle
  cover property (!sdram_rst && $changed(fml_adr[0]) && !$changed(mgmt_address));

  // Address responds to bit[1] change
  cover property (!sdram_rst && $changed(fml_adr[1]) &&  $changed(mgmt_address));

  // Ack/we mapping observed high
  cover property (!sdram_rst && data_ack && fml_ack);
  cover property (!sdram_rst && mgmt_we  && fml_we);

endmodule

// Example bind (place in a package or a tb file):
// bind hpdmc_busif hpdmc_busif_sva #(.sdram_depth(sdram_depth)) ();