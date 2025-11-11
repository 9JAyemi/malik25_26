// SVA for module signalinput
// Bind this checker: bind signalinput signalinput_sva sva();

module signalinput_sva;

  // constants from DUT decode
  localparam int unsigned DIV_T0 = 21'd32000;    // 2'b00
  localparam int unsigned DIV_T1 = 21'd16000;    // 2'b01 (per RTL constant)
  localparam int unsigned DIV_T2 = 21'd2000000;  // 2'b10
  localparam int unsigned DIV_T3 = 21'd8000;     // 2'b11

  default clocking cb @(posedge sysclk); endclocking

  // Basic sanity
  assert property ( !$isunknown({testmode, sigin, sigin1, state, divide}) );

  // Initial values at time 0 (checked using past of initstate on first clock)
  assert property ( $past($initstate) |-> ($past(state)==21'd0 && $past(sigin)==1'b0 && $past(divide)==DIV_T0) );

  // Combinational decode: testmode -> divide
  assert property ( (testmode==2'b00) |-> (divide==DIV_T0) );
  assert property ( (testmode==2'b01) |-> (divide==DIV_T1) );
  assert property ( (testmode==2'b10) |-> (divide==DIV_T2) );
  assert property ( (testmode==2'b11) |-> (divide==DIV_T3) );

  // Only legal divide values appear
  assert property ( divide inside {DIV_T0, DIV_T1, DIV_T2, DIV_T3} );

  // Output mirrors internal
  assert property ( sigin1 == sigin );

  // State invariants (independent of divide changes)
  assert property ( state[0] == 1'b0 ); // even count only

  // Next-state relation (comparison uses prior divide, as in RTL)
  assert property ( ($past(state)==$past(divide)-21'd2) |-> (state==21'd0) );
  assert property ( ($past(state)!=$past(divide)-21'd2) |-> (state==$past(state)+21'd2) );

  // Only way to reach state==0 (except time 0) is from divide-2
  assert property ( (!$past($initstate) && state==21'd0) |-> ($past(state)==$past(divide)-21'd2) );

  // sigin toggles iff previous state was 0
  assert property ( ($past(state)==21'd0) |-> (sigin != $past(sigin)) );
  assert property ( ($past(state)!=21'd0) |-> (sigin == $past(sigin)) );

  // Coverage: see a wrap/toggle in each mode
  cover property ( testmode==2'b00 ##1 $past(state)==$past(divide)-21'd2 ##1 state==21'd0 );
  cover property ( testmode==2'b01 ##1 $past(state)==$past(divide)-21'd2 ##1 state==21'd0 );
  cover property ( testmode==2'b10 ##1 $past(state)==$past(divide)-21'd2 ##1 state==21'd0 );
  cover property ( testmode==2'b11 ##1 $past(state)==$past(divide)-21'd2 ##1 state==21'd0 );

  // Coverage: mode switch during operation still leads to a proper wrap
  cover property ( $changed(testmode) ##[1:$] ($past(state)==$past(divide)-21'd2) ##1 state==21'd0 );

endmodule