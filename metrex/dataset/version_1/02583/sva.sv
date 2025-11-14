// SVA for clock_gate_d_ff_en_W32_0_6
module clock_gate_d_ff_en_W32_0_6_sva (
  input logic        CLK,
  input logic        EN,
  input logic        TE,
  input logic [31:0] DATA,
  input logic        ENCLK,
  input logic        D
);
  default clocking cb @(posedge CLK); endclocking

  // ENCLK must reflect EN & ~TE at each posedge; and be known when controls are known
  a_enclk_value:        assert property ( (!$isunknown({EN,TE})) |-> (ENCLK === (EN && !TE)) );
  a_enclk_known_when_ok:assert property ( (!$isunknown({EN,TE})) |-> !$isunknown(ENCLK) );

  // ENCLK can only change on posedge CLK (no negedge or mid-cycle glitches)
  a_enclk_glitch_free:  assert property (@(negedge CLK) $stable(ENCLK));

  // D capture/hold behavior
  a_d_captures_lsb:     assert property ( (EN && !TE && !$isunknown(DATA[0])) |=> (D === $past(DATA[0])) );
  a_d_holds_otherwise:  assert property ( (!EN || TE) |=> (D === $past(D)) );
  a_d_change_has_cause: assert property ( $changed(D) |-> $past(EN && !TE) );

  // Detect likely width mismatch use: only DATA[0] is captured; flag if upper bits set when capturing
  a_truncation_guard:   assert property ( (EN && !TE) |-> (DATA[31:1] == '0) );

  // Basic covers for key scenarios
  c_capture:            cover property (EN && !TE);
  c_gate:               cover property (TE);
  c_hold:               cover property (!EN && !TE);
  c_enclk_hilo:         cover property ( (EN && !TE) ##1 (!EN && !TE) ##1 (EN && !TE) );
  c_d_change_capture:   cover property ( (EN && !TE && $changed(DATA[0])) ##1 (D === $past(DATA[0])) );
endmodule

bind clock_gate_d_ff_en_W32_0_6 clock_gate_d_ff_en_W32_0_6_sva sva_i (
  .CLK(CLK),
  .EN(EN),
  .TE(TE),
  .DATA(DATA),
  .ENCLK(ENCLK),
  .D(D)
);