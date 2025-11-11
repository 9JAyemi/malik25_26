// SVA for sky130_fd_sc_hs__sdlclkp
// Bind into the DUT to access internal gate_state
module sky130_fd_sc_hs__sdlclkp_sva
(
  input logic CLK,
  input logic GATE,
  input logic SCE,
  input logic GCLK,
  input logic gate_state,
  input logic VPWR,
  input logic VGND
);
  // Sample on CLK edges and SCE posedge to catch async enable effects and clock activity
  default clocking cb @(posedge CLK or negedge CLK or posedge SCE); endclocking

  function automatic bit power_ok();
    return (VPWR === 1'b1 && VGND === 1'b0);
  endfunction

  // 1) Functional equivalence: output equals gate_state && CLK at all times
  //    (disabled while any relevant signal is X or power bad)
  assert property ( @cb disable iff (!power_ok() || $isunknown({CLK,gate_state})))
    GCLK == (gate_state && CLK);

  // 2) Latch behavior: on SCE posedge, gate_state updates to current GATE (nonblocking -> ##0)
  assert property ( @(posedge SCE) disable iff (!power_ok() || $isunknown({SCE,GATE})) ##0
    gate_state == $sampled(GATE));

  // 3) gate_state may only change when SCE rises
  assert property ( @cb disable iff (!power_ok() || $isunknown({SCE,gate_state})))
    !$rose(SCE) |-> $stable(gate_state);

  // 4) When disabled, GCLK must be 0
  assert property ( @cb disable iff (!power_ok() || $isunknown({CLK,gate_state})))
    (!gate_state) |-> (GCLK == 1'b0);

  // 5) When enabled, GCLK mirrors CLK
  assert property ( @cb disable iff (!power_ok() || $isunknown({CLK,gate_state})))
    gate_state |-> (GCLK == CLK);

  // 6) No X/Z on outputs when inputs and power are known/good
  assert property ( @cb disable iff (!power_ok() || $isunknown({CLK,SCE,GATE,gate_state})))
    !$isunknown(GCLK);

  // Coverage
  // a) Capture both enable and disable on SCE edges
  cover property ( @(posedge SCE) $sampled(GATE) == 1 );
  cover property ( @(posedge SCE) $sampled(GATE) == 0 );
  // b) See GCLK activity while enabled
  cover property ( @cb gate_state && $changed(GCLK) );
  // c) Enable or disable while CLK is high (asynchronous effect scenarios)
  cover property ( @(posedge SCE) $sampled(GATE)==1 && CLK );
  cover property ( @(posedge SCE) $sampled(GATE)==0 && CLK );

endmodule

bind sky130_fd_sc_hs__sdlclkp sky130_fd_sc_hs__sdlclkp_sva sva_i
(
  .CLK(CLK),
  .GATE(GATE),
  .SCE(SCE),
  .GCLK(GCLK),
  .gate_state(gate_state),
  .VPWR(VPWR),
  .VGND(VGND)
);