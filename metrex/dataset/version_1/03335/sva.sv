// SVA for shift_register
// Concise, high-signal-quality checks + functional coverage

module shift_register_sva #(parameter WIDTH = 4) (
  input logic              clk,
  input logic              RESET,
  input logic              LOAD,
  input logic              SHIFT,
  input logic [WIDTH-1:0]  DIN,
  input logic [WIDTH-1:0]  Q
);

  default clocking cb @(posedge clk); endclocking

  // Basic X/validity checks on controls and DIN when used
  assert property ( !$isunknown({RESET, LOAD, SHIFT}) )
    else $error("X/Z on control inputs");
  assert property ( (!RESET && LOAD) |-> !$isunknown(DIN) )
    else $error("DIN X/Z when LOAD active");

  // Reset dominates: synchronous clear and hold at 0 while RESET high
  assert property ( RESET |-> (Q == '0) )
    else $error("Q not 0 on RESET cycle");
  assert property ( RESET |=> (RESET throughout (Q == '0)) )
    else $error("Q not held at 0 during RESET");

  // LOAD behavior and priority over SHIFT when not in RESET
  assert property ( (!RESET && LOAD) |=> (Q == $past(DIN)) )
    else $error("LOAD failed to update Q with DIN");
  assert property ( (!RESET && LOAD && SHIFT) |=> (Q == $past(DIN)) )
    else $error("LOAD did not dominate SHIFT");

  // SHIFT behavior (zero-fill left shift) when not RESET/LOAD
  assert property ( (!RESET && !LOAD && SHIFT) |=> (Q == { $past(Q)[WIDTH-2:0], 1'b0 }) )
    else $error("SHIFT incorrect (expected left shift with 0 fill)");
  // After WIDTH consecutive shifts (no RESET/LOAD), Q must be zero
  assert property ( (!RESET && !LOAD && SHIFT)[*WIDTH] |=> (Q == '0) )
    else $error("After WIDTH shifts without LOAD/RESET, Q not zero");

  // Hold behavior when no control asserted
  assert property ( (!RESET && !LOAD && !SHIFT) |=> (Q == $past(Q)) )
    else $error("Q did not hold value when no control active");

  // Optional sanity: LSB becomes 0 on any qualifying shift
  assert property ( (!RESET && !LOAD && SHIFT) |=> (Q[0] == 1'b0) )
    else $error("LSB not 0 after shift");

  // Functional coverage
  cover property ( RESET );
  cover property ( !RESET && LOAD );
  cover property ( !RESET && !LOAD && SHIFT );
  cover property ( !RESET && !LOAD && !SHIFT );
  cover property ( !RESET && LOAD && SHIFT );   // priority case
  cover property ( RESET && LOAD );             // reset dominance
  // Load then drain to zero via WIDTH shifts
  cover property ( (!RESET && LOAD), ##1 (!RESET && !LOAD && SHIFT)[*WIDTH] ##1 (Q == '0) );

endmodule

// Bind into DUT
bind shift_register shift_register_sva #(.WIDTH(4)) i_shift_register_sva (
  .clk   (clk),
  .RESET (RESET),
  .LOAD  (LOAD),
  .SHIFT (SHIFT),
  .DIN   (DIN),
  .Q     (Q)
);