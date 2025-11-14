module clock_divider_sva (
  input  logic       CLK,
  input  logic       reset,
  input  logic       CLK_div,
  input  logic [3:0] counter
);

  default clocking cb @(posedge CLK); endclocking

  // No X on key regs when not in reset (skip time 0)
  assert property ( disable iff ($initstate) !reset |-> !$isunknown({CLK_div, counter}) );

  // Counter bounded 0..4
  assert property ( counter <= 4 );

  // Reset behavior: drive zeros by next clock, and hold zeros while reset stays high
  assert property ( reset |=> (counter==0 && CLK_div==0) );
  assert property ( reset && $past(reset) |-> (counter==0 && CLK_div==0) );

  // Normal increment when not hitting terminal count
  assert property ( disable iff (reset)
                    (counter != 4) |=> (counter == $past(counter)+1 && $stable(CLK_div)) );

  // Terminal count: reload to 0 and toggle output
  assert property ( disable iff (reset)
                    (counter == 4) |=> (counter == 0 && CLK_div == !$past(CLK_div)) );

  // Output toggles only on terminal count (and coincides with 4->0 reload)
  assert property ( disable iff (reset)
                    $changed(CLK_div) |-> ($past(counter)==4 && counter==0) );

  // Exact spacing between CLK_div toggles = 5 input clocks (50% duty over 10)
  assert property ( disable iff (reset)
                    $changed(CLK_div) |=> (!$changed(CLK_div))[*4] ##1 $changed(CLK_div) );

  // First non-reset cycle after deassert: count 0->1, output still 0
  assert property ( $fell(reset) |=> (counter==1 && CLK_div==0) );

  // Coverage: one full half-period sequence and both edges of CLK_div
  cover property ( disable iff (reset)
                   (counter==0) ##1 (counter==1) ##1 (counter==2) ##1 (counter==3) ##1
                   (counter==4) ##1 (counter==0 && $changed(CLK_div)) );

  cover property ( disable iff (reset) $rose(CLK_div) );
  cover property ( disable iff (reset) $fell(CLK_div) );

endmodule

// Bind into the DUT (accessing internal 'counter')
bind clock_divider clock_divider_sva sva_i (
  .CLK     (CLK),
  .reset   (reset),
  .CLK_div (CLK_div),
  .counter (counter)
);