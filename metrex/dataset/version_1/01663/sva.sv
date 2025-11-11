// SVA for top_module and its sub-blocks (concise, high-signal-coverage)
module top_module_sva #(parameter int W=4) (
  input  logic              CLK,
  input  logic              RST,
  input  logic              UP,
  input  logic              LD,
  input  logic              select,
  input  logic [W-1:0]      a,
  input  logic [W-1:0]      b,
  input  logic [W-1:0]      D,
  input  logic [W-1:0]      final_output,
  input  logic [W-1:0]      binary_sum,
  input  logic [W-1:0]      counter_output
);

  default clocking cb @(posedge CLK); endclocking

  // --------------------
  // Combinational adder and top-level mux checks
  // --------------------
  // Adder is pure modulo-2^W addition
  assert property (binary_sum == ((a + b) & {W{1'b1}}))
    else $error("binary_adder: sum != (a+b) mod 2^W");

  // Mux selects between adder and counter outputs
  assert property (final_output == (select ? counter_output : binary_sum))
    else $error("top mux: final_output != selected source");

  // --------------------
  // up_down_counter behavior (synchronous, priority: RST > UP > LD > else load D)
  // --------------------
  // Synchronous reset dominates
  assert property (RST |=> counter_output == '0)
    else $error("counter: reset failed to drive 0");

  // UP increments regardless of LD (UP has priority over LD)
  assert property (disable iff (RST)
                   UP |=> counter_output == (($past(counter_output) + (W+1)'(1)) & {W{1'b1}}))
    else $error("counter: UP increment mismatch");

  // LD decrements only when UP is low
  assert property (disable iff (RST)
                   (!UP && LD) |=> counter_output == (($past(counter_output) - (W+1)'(1)) & {W{1'b1}}))
    else $error("counter: LD decrement mismatch");

  // Else branch loads D when both UP and LD are low
  assert property (disable iff (RST)
                   (!UP && !LD) |=> counter_output == $past(D))
    else $error("counter: load D mismatch");

  // --------------------
  // Minimal X-prop sanity on critical outputs (outside reset)
  // --------------------
  assert property (disable iff (RST) !$isunknown(counter_output))
    else $error("counter_output is X/Z outside reset");
  assert property (!$isunknown(final_output))
    else $error("final_output is X/Z");

  // --------------------
  // Coverage
  // --------------------
  // Exercise mux both ways
  cover property (select && (final_output == counter_output));
  cover property (!select && (final_output == binary_sum));

  // Adder overflow case covered
  cover property ( ({1'b0,a} + {1'b0,b})[W] );

  // Counter: increment, decrement, load
  cover property (disable iff (RST) UP);
  cover property (disable iff (RST) (!UP && LD));
  cover property (disable iff (RST) (!UP && !LD));

  // Counter wrap-around both directions
  cover property (disable iff (RST)
                  ($past(counter_output) == {W{1'b1}} && UP) |=> counter_output == '0);
  cover property (disable iff (RST)
                  ($past(counter_output) == '0 && !UP && LD) |=> counter_output == {W{1'b1}});

  // Priority case: UP and LD both high -> increment
  cover property (disable iff (RST)
                  (UP && LD) |=> counter_output == (($past(counter_output) + (W+1)'(1)) & {W{1'b1}}));

endmodule

// Bind to DUT; connects to ports and internal nets by name (binary_sum, counter_output)
bind top_module top_module_sva #(.W(4)) top_module_sva_i (.*);