// SVA for clock_divider
module clock_divider_sva #(parameter int DIVISOR = 40000000) (
  input  logic CLK,
  input  logic RESET,
  input  logic CE,
  input  logic CLOCK,
  input  int   counter_ce,
  input  int   counter_clk
);

  localparam int HALF = (DIVISOR >> 1);

  // Parameter sanity
  initial begin
    assert (DIVISOR >= 2)
      else $fatal(1, "clock_divider: DIVISOR must be >= 2");
    assert ((DIVISOR % 2) == 0)
      else $error("clock_divider: DIVISOR is odd; CLOCK divide may be inaccurate");
  end

  default clocking cb @(posedge CLK); endclocking
  default disable iff (RESET);

  // During RESET, all state/output forced to 0
  assert property (disable iff (0) @(posedge CLK) RESET |-> (CE==0 && CLOCK==0 && counter_ce==0 && counter_clk==0));

  // CE: value, pulse width, and periodicity
  assert property (CE == (counter_ce == 0));
  assert property (CE |=> !CE);
  assert property (CE |=> !CE[* (DIVISOR-1)] ##1 CE);

  // counter_ce: range and next-state
  assert property (counter_ce >= 0 && counter_ce < DIVISOR);
  assert property ((!$past(RESET) && (counter_ce != DIVISOR-1)) |=> counter_ce == $past(counter_ce)+1);
  assert property ((!$past(RESET) && (counter_ce == DIVISOR-1)) |=> counter_ce == 0);
  assert property (($rose(CE) && !$past(RESET)) |-> $past(counter_ce) == DIVISOR-1);

  // CLOCK toggling exactly when counter_clk==0; otherwise holds
  assert property ((!$past(RESET) && (counter_clk == 0)) |-> CLOCK != $past(CLOCK));
  assert property ((!$past(RESET) && (counter_clk != 0)) |-> CLOCK == $past(CLOCK));

  // counter_clk: range and next-state
  assert property (counter_clk >= 0 && counter_clk < HALF);
  assert property ((!$past(RESET) && (counter_clk != (HALF-1))) |=> counter_clk == $past(counter_clk)+1);
  assert property ((!$past(RESET) && (counter_clk == (HALF-1))) |=> counter_clk == 0);

  // Exact half-period between CLOCK toggles (counter_clk==0 repeats every HALF cycles)
  assert property (counter_clk==0 |=> (counter_clk!=0)[* (HALF-1)] ##1 counter_clk==0);

  // Minimal coverage
  cover property (!RESET ##1 CE);
  cover property (counter_ce == (DIVISOR-1) ##1 counter_ce == 0);
  cover property (counter_clk == (HALF-1) ##1 counter_clk == 0);
  cover property (counter_clk==0 ##HALF counter_clk==0);

endmodule

// Bind into DUT
bind clock_divider clock_divider_sva #(.DIVISOR(DIVISOR)) clock_divider_sva_i (
  .CLK       (CLK),
  .RESET     (RESET),
  .CE        (CE),
  .CLOCK     (CLOCK),
  .counter_ce(counter_ce),
  .counter_clk(counter_clk)
);