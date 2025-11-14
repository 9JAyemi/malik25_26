// SVA for binary_counter
// Bind example:
// bind binary_counter binary_counter_sva #(.n(n), .mod(mod)) u_sva (.*);

module binary_counter_sva #(parameter int n = 4, parameter int mod = 0)
(
  input logic                 clk,
  input logic                 rst,
  input logic                 ctrl,
  input logic                 load,
  input logic [n-1:0]         val,
  input logic [n-1:0]         out
);
  localparam logic [n-1:0] MOD      = mod;
  localparam bit           MOD_EN   = (mod != 0);
  localparam logic [n-1:0] ALL_ONES = {n{1'b1}};

  default clocking cb @(posedge clk); endclocking

  // Parameter sanity (static)
  initial begin
    assert (mod >= 0) else $error("binary_counter: mod must be >= 0");
    assert (mod < (1<<n)) else $error("binary_counter: mod must fit within n bits");
  end

  // Controls should be known (helps catch X/Z driving ambiguous behavior)
  assert property (!$isunknown({rst,load,ctrl})))
    else $error("binary_counter: X/Z on control inputs");

  // Reset dominates: next state is 0
  assert property ($past(rst) |-> out == '0)
    else $error("binary_counter: reset must clear to 0");

  // While reset held, output stays 0
  assert property (rst |-> out == '0)
    else $error("binary_counter: output must be 0 while reset asserted");

  // Modulo override: if previous out == MOD (and enabled), next state forced to 0
  assert property (MOD_EN && $past(out) == MOD |-> out == '0)
    else $error("binary_counter: modulo override to 0 violated");

  // Load (when not overridden by modulo) takes priority over up/down
  assert property ($past(!rst && load) && !(MOD_EN && $past(out)==MOD) |-> out == $past(val))
    else $error("binary_counter: load behavior violated");

  // Count up (when ctrl=1), unless reset/load/mod override applied
  assert property ($past(!rst && !load && ctrl) && !(MOD_EN && $past(out)==MOD) |-> out == ($past(out) + 1'b1))
    else $error("binary_counter: increment behavior violated");

  // Count down (when ctrl=0), unless reset/load/mod override applied
  assert property ($past(!rst && !load && !ctrl) && !(MOD_EN && $past(out)==MOD) |-> out == ($past(out) - 1'b1))
    else $error("binary_counter: decrement behavior violated");

  // If ctrl is X (and no rst/load/mod), hold previous value (matches RTL if/else behavior)
  assert property ($past(!rst && !load) && $isunknown($past(ctrl)) && !(MOD_EN && $past(out)==MOD) |-> out == $past(out))
    else $error("binary_counter: unexpected change when ctrl is X");

  // Output should never be X/Z after clock
  assert property (!rst |-> !$isunknown(out))
    else $error("binary_counter: X/Z on output");

  // Coverage
  cover property (!rst && load);                                // load seen
  cover property (!rst && !load && ctrl);                       // increment path seen
  cover property (!rst && !load && !ctrl);                      // decrement path seen
  cover property (MOD_EN && out == MOD ##1 out == '0);          // modulo override event
  cover property (!MOD_EN && $past(!rst && !load && ctrl) &&
                  $past(out) == ALL_ONES ##1 out == '0);        // natural wrap (up) when mod disabled
  cover property (!MOD_EN && $past(!rst && !load && !ctrl) &&
                  $past(out) == '0 ##1 out == ALL_ONES);        // natural wrap (down) when mod disabled
endmodule