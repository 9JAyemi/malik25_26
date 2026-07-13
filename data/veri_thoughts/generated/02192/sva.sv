module clock_gate_sva (
  input logic CLK,
  input logic EN,
  input logic TE,
  input logic ENCLK
);

  // TE high forces ENCLK low.
  check_te_forces_low: assert property (
    @(posedge CLK) TE |-> (ENCLK == 1'b0)
  );

  // EN low forces ENCLK low (regardless of TE).
  check_en_low_forces_low: assert property (
    @(posedge CLK) !EN |-> (ENCLK == 1'b0)
  );

  // When enabled and not in test, ENCLK mirrors CLK.
  check_enable_passes_clk: assert property (
    @(posedge CLK) (!TE && EN) |-> (ENCLK == CLK)
  );

  // ENCLK high implies EN=1, TE=0, and CLK is high.
  check_enclk_high_implies_enable: assert property (
    @(posedge CLK) (ENCLK == 1'b1) |-> (EN && !TE && (CLK == 1'b1))
  );

  // A rising TE immediately drives ENCLK low.
  check_te_rise_clears_enclk: assert property (
    @(posedge CLK) $rose(TE) |=> (ENCLK == 1'b0)
  );

  // A falling EN immediately drives ENCLK low.
  check_en_fall_clears_enclk: assert property (
    @(posedge CLK) $fell(EN) |=> (ENCLK == 1'b0)
  );

  // A rising EN with TE low immediately makes ENCLK equal to CLK.
  check_en_rise_passes_clk: assert property (
    @(posedge CLK) ($rose(EN) && !TE) |=> (ENCLK == CLK)
  );

  // ENCLK can only rise when EN=1 and TE=0 (and CLK=1 at this sample).
  check_enclk_rise_requires_enable: assert property (
    @(posedge CLK) $rose(ENCLK) |-> (EN && !TE && (CLK == 1'b1))
  );

  // ENCLK can only fall when disabled by EN or TE.
  check_enclk_fall_requires_disable: assert property (
    @(posedge CLK) $fell(ENCLK) |-> (!EN || TE)
  );

  // With TE low, ENCLK equals EN at CLK posedge (since ENCLK = EN & CLK).
  check_te_low_maps_to_en: assert property (
    @(posedge CLK) !TE |-> (ENCLK == EN)
  );

endmodule