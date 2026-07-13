module clock_gate_sva (
  input logic CLK,
  input logic EN,
  input logic TE,
  output logic ENCLK
);
  // Ensure ENCLK is only enabled when EN is high and TE is low
  property p_enclk_enable;
    @(posedge CLK) disable iff (!EN) ENCLK == (EN && !TE);
  endproperty
  assert property (p_enclk_enable) else $error("ENCLK should only be enabled when EN is high and TE is low");

  // Ensure ENCLK is disabled when EN is low
  property p_enclk_disable;
    @(posedge CLK) disable iff (!EN) ENCLK == 0;
  endproperty
  assert property (p_enclk_disable) else $error("ENCLK should be disabled when EN is low");

  // Ensure ENCLK is not affected by TE when EN is low
  property p_enclk_te_when_en_low;
    @(posedge CLK) disable iff (!EN) ENCLK == ENCLK;
  endproperty
  assert property (p_enclk_te_when_en_low) else $error("ENCLK should not be affected by TE when EN is low");

  // Ensure ENCLK is not affected by CK when EN is low
  property p_enclk_ck_when_en_low;
    @(posedge CLK) disable iff (!EN) ENCLK == ENCLK;
  endproperty
  assert property (p_enclk_ck_when_en_low) else $error("ENCLK should not be affected by CK when EN is low");

  // Ensure ENCLK is not affected by E when EN is low
  property p_enclk_e_when_en_low;
    @(posedge CLK) disable iff (!EN) ENCLK == ENCLK;
  endproperty
  assert property (p_enclk_e_when_en_low) else $error("ENCLK should not be affected by E when EN is low");

  // Ensure ENCLK is not affected by SE when EN is low
  property p_enclk_se_when_en_low;
    @(posedge CLK) disable iff (!EN) ENCLK == ENCLK;
  endproperty
  assert property (p_enclk_se_when_en_low) else $error("ENCLK should not be affected by SE when EN is low");

  // Ensure ENCLK is not affected by CK when TE is high
  property p_enclk_ck_when_te_high;
    @(posedge CLK) disable iff (!TE) ENCLK == ENCLK;
  endproperty
  assert property (p_enclk_ck_when_te_high) else $error("ENCLK should not be affected by CK when TE is high");

  // Ensure ENCLK is not affected by E when TE is high
  property p_enclk_e_when_te_high;
    @(posedge CLK) disable iff (!TE) ENCLK == ENCLK;
  endproperty
  assert property (p_enclk_e_when_te_high) else $error("ENCLK should not be affected by E when TE is high");

  // Ensure ENCLK is not affected by SE when TE is high
  property p_enclk_se_when_te_high;
    @(posedge CLK) disable iff (!TE) ENCLK == ENCLK;
  endproperty
  assert property (p_enclk_se_when_te_high) else $error("ENCLK should not be affected by SE when TE is high");

  // Ensure ENCLK is not affected by E when TE is high
  property p_enclk_e_when_te_high;
    @(posedge CLK) disable iff (!TE) ENCLK == ENCLK;
  endproperty
  assert property (p_enclk_e_when_te_high) else $error("ENCLK should not be affected by E when TE is high");

endmodule