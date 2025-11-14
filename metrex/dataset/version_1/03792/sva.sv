// SVA for clock_divider: concise, high-quality checks and coverage

module clock_divider_sva #(parameter int unsigned DIVISOR = 8)
(
  input  logic                      CLK,
  input  logic                      RESET,
  input  logic                      CE,
  input  logic                      CLOCK,
  input  logic [DIVISOR-1:0]        counter
);

  default clocking cb @(posedge CLK); endclocking

  // Reset holds both outputs low
  assert property (@cb !RESET |-> (counter == '0 && CLOCK == 1'b0));

  // Counter must stay in range [0, DIVISOR-1]
  assert property (@cb disable iff (!RESET) counter < DIVISOR);

  // When CE=0, state holds
  assert property (@cb disable iff (!RESET) !CE |=> $stable({counter, CLOCK}));

  // Increment when not wrapping
  assert property (@cb disable iff (!RESET)
                   CE && counter != DIVISOR-1 |=> counter == $past(counter) + 1 && CLOCK == $past(CLOCK));

  // Wrap and toggle on terminal count
  assert property (@cb disable iff (!RESET)
                   CE && counter == DIVISOR-1 |=> counter == '0 && CLOCK != $past(CLOCK));

  // Any toggle must be caused by CE and terminal count in the prior cycle
  assert property (@cb disable iff (!RESET)
                   $changed(CLOCK) |-> $past(CE) && $past(counter) == DIVISOR-1);

  // Coverage

  // See reset activity
  cover property (@cb $fell(RESET));
  cover property (@cb !RESET ##1 RESET);

  // See a wrap/toggle event
  cover property (@cb disable iff (!RESET)
                  CE && counter == DIVISOR-1 |=> $changed(CLOCK) && counter == '0);

  // See idle gaps followed by counting
  cover property (@cb disable iff (!RESET) !CE ##1 !CE ##1 CE);

  // Exactly DIVISOR CE pulses between successive toggles (non-consecutive CE allowed)
  cover property (@cb disable iff (!RESET)
                  $changed(CLOCK) |=> (CE [->DIVISOR]) ##0 $changed(CLOCK));

endmodule

bind clock_divider clock_divider_sva #(.DIVISOR(DIVISOR))
  clock_divider_sva_i (.CLK(CLK), .RESET(RESET), .CE(CE), .CLOCK(CLOCK), .counter(counter));