// Bindable SVA for UniversalCounter8bits
module UniversalCounter8bits_sva (
  input logic        CLOCK, Reset, S1, S0,
  input logic [7:0]  P, BeginCount, EndCount,
  input logic [7:0]  Q,
  input logic        TerminalCount
);

  // Asynchronous reset must immediately drive outputs low
  property p_async_reset_immediate;
    @(posedge Reset) (Q==8'd0 && TerminalCount==1'b0);
  endproperty
  assert property (p_async_reset_immediate);

  // While reset is asserted at a clock edge, outputs held low
  property p_reset_hold;
    @(posedge CLOCK) Reset |-> (Q==8'd0 && TerminalCount==1'b0);
  endproperty
  assert property (p_reset_hold);

  // No X/Z on outputs after reset released
  property p_no_x;
    @(posedge CLOCK) disable iff (Reset) !$isunknown({Q,TerminalCount});
  endproperty
  assert property (p_no_x);

  // Hold mode: Q stable, TC=0
  property p_hold;
    @(posedge CLOCK) disable iff (Reset)
      ({S1,S0}==2'b00) |=> ($stable(Q) && TerminalCount==1'b0);
  endproperty
  assert property (p_hold);

  // Parallel load: Q loads P, TC=0
  property p_load;
    @(posedge CLOCK) disable iff (Reset)
      ({S1,S0}==2'b11) |=> (Q==P && TerminalCount==1'b0);
  endproperty
  assert property (p_load);

  // Count up: non-wrap increments, TC=0
  property p_up_nwrap;
    @(posedge CLOCK) disable iff (Reset)
      ({S1,S0}==2'b01 && Q!=EndCount) |=> (Q==$past(Q)+8'd1 && TerminalCount==1'b0);
  endproperty
  assert property (p_up_nwrap);

  // Count up: wrap to BeginCount, TC=1
  property p_up_wrap;
    @(posedge CLOCK) disable iff (Reset)
      ({S1,S0}==2'b01 && Q==EndCount) |=> (Q==BeginCount && TerminalCount==1'b1);
  endproperty
  assert property (p_up_wrap);

  // Count down: non-wrap decrements, TC=0
  property p_dn_nwrap;
    @(posedge CLOCK) disable iff (Reset)
      ({S1,S0}==2'b10 && Q!=BeginCount) |=> (Q==$past(Q)-8'd1 && TerminalCount==1'b0);
  endproperty
  assert property (p_dn_nwrap);

  // Count down: wrap to EndCount, TC=1
  property p_dn_wrap;
    @(posedge CLOCK) disable iff (Reset)
      ({S1,S0}==2'b10 && Q==BeginCount) |=> (Q==EndCount && TerminalCount==1'b1);
  endproperty
  assert property (p_dn_wrap);

  // TC can only assert on a wrap from the prior cycle and in a count mode
  property p_tc_only_on_wrap;
    @(posedge CLOCK) disable iff (Reset)
      TerminalCount |-> (
        ($past({S1,S0})==2'b01 && $past(Q)==$past(EndCount)) ||
        ($past({S1,S0})==2'b10 && $past(Q)==$past(BeginCount))
      );
  endproperty
  assert property (p_tc_only_on_wrap);

  // Basic functional coverage
  cover property (@(posedge CLOCK) ({S1,S0}==2'b00) ##1 $stable(Q));                  // hold seen
  cover property (@(posedge CLOCK) ({S1,S0}==2'b11) |=> (Q==P));                      // load seen
  cover property (@(posedge CLOCK) disable iff (Reset)
                  ({S1,S0}==2'b01 && Q==EndCount) |=> (Q==BeginCount && TerminalCount)); // up wrap
  cover property (@(posedge CLOCK) disable iff (Reset)
                  ({S1,S0}==2'b10 && Q==BeginCount) |=> (Q==EndCount && TerminalCount)); // down wrap
  cover property (@(posedge Reset) 1);                                                // reset asserted

endmodule

// Bind into DUT (tool-dependent; adjust if needed)
bind UniversalCounter8bits UniversalCounter8bits_sva sva_inst (
  .CLOCK(CLOCK), .Reset(Reset), .S1(S1), .S0(S0),
  .P(P), .BeginCount(BeginCount), .EndCount(EndCount),
  .Q(Q), .TerminalCount(TerminalCount)
);