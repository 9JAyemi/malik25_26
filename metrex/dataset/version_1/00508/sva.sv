// SVA for sky130_fd_sc_hs__dfsbp
// Focus: output complementarity, power behavior, async set behavior, change legality, basic data capture after set release, and coverage.

module sky130_fd_sc_hs__dfsbp_sva (
  input VPWR,
  input VGND,
  input Q,
  input Q_N,
  input CLK,
  input D,
  input SET_B
);
  wire awake = (VPWR === 1'b1);

  // Outputs are always complementary
  assert property (@(posedge CLK) (Q_N === ~Q));
  assert property (@(posedge Q or negedge Q or posedge Q_N or negedge Q_N) (Q_N === ~Q));

  // Power-down forces Q=0, Q_N=1 immediately and while off
  assert property (@(negedge awake) (Q === 1'b0 && Q_N === 1'b1));
  assert property (@(posedge CLK) (!awake) |-> (Q === 1'b0 && Q_N === 1'b1));

  // Asynchronous SET (active low) forces Q=1
  assert property (@(negedge SET_B) awake |-> (Q === 1'b1));
  assert property (@(posedge CLK) awake && (SET_B === 1'b0) |-> (Q === 1'b1));
  // If SET_B is unknown while awake, Q must still be 1 per cond1 check in DUT
  assert property (@(posedge CLK) awake && $isunknown(SET_B) |-> (Q === 1'b1));

  // No spurious Q changes when SET_B is high: Q may change only on CLK posedge
  assert property (@(posedge Q or negedge Q) awake && (SET_B === 1'b1) |-> $rose(CLK));

  // After SET_B low->high release, on the first sampled CLK posedge Q must capture D
  // (Sampled at CLK edges; may miss sub-cycle SET_B glitches, but checks intended behavior)
  assert property (@(posedge CLK) disable iff (!awake)
                   (SET_B === 1'b1 && $past(SET_B,1) === 1'b0) |-> (Q === D));

  // Known outputs when inputs known and awake
  assert property (@(posedge CLK) disable iff (!awake)
                   (!$isunknown({SET_B, D})) |-> (!$isunknown({Q, Q_N})));

  // Coverage
  // 1) SET low pulse -> release -> next CLK captures D
  cover property (@(posedge CLK) disable iff (!awake)
                  $fell(SET_B) ##[1:$] $rose(SET_B) ##1 (Q === D));
  // 2) Power cycle
  cover property (@(posedge CLK) $fell(awake) ##[1:50] $rose(awake));
  // 3) Q toggles while awake with SET_B high (driven by CLK)
  cover property (@(posedge CLK) disable iff (!awake)
                  (SET_B === 1'b1) && $changed(Q));
endmodule

bind sky130_fd_sc_hs__dfsbp sky130_fd_sc_hs__dfsbp_sva sva_i (.*);