// SystemVerilog Assertions for the provided design
// Focused on concise, high-quality checks and coverage

module top_module_sva (
  input  logic        CLK,
  input  logic        RST,
  input  logic        DIR,
  input  logic [15:0] a,
  input  logic [15:0] b,
  input  logic [15:0] Q,
  input  logic        lt,
  input  logic        eq,
  input  logic        gt,
  input  logic [15:0] max_output
);

  default clocking cb @(posedge CLK); endclocking

  //========================
  // up_down_counter checks
  //========================

  // Reset drives Q to 0 on the next clock and holds at 0 while RST stays high
  assert property (RST |=> Q == 16'h0000)
    else $error("Q not zero 1-cycle after RST");

  assert property ($past(RST) && RST |-> Q == 16'h0000)
    else $error("Q did not hold at zero during sustained RST");

  // Count up on DIR=1 with wrap at 16'hFFFF
  assert property (disable iff (RST)
                   $past(DIR) |=> Q == (($past(Q)==16'hFFFF) ? 16'h0000 : $past(Q)+16'h0001))
    else $error("Increment/wrap violation");

  // Count down on DIR=0 when Q!=0
  assert property (disable iff (RST)
                   !$past(DIR) && ($past(Q)!=16'h0000) |=> Q == $past(Q)-16'h0001)
    else $error("Decrement violation");

  // Hold at 0 on DIR=0 when Q==0
  assert property (disable iff (RST)
                   !$past(DIR) && ($past(Q)==16'h0000) |=> Q == 16'h0000)
    else $error("Hold-at-zero violation when DIR=0");

  //========================
  // comparator checks
  //========================

  // Exact functional equivalence and mutual exclusivity
  assert property (lt == (Q <  b)) else $error("lt mismatch");
  assert property (eq == (Q == b)) else $error("eq mismatch");
  assert property (gt == (Q >  b)) else $error("gt mismatch");
  assert property ($onehot({lt,eq,gt})) else $error("Comparator outputs not one-hot");

  //========================
  // max_value checks
  //========================

  // Behavior per RTL: select b when gt, else a (note: this is effectively min(Q,b))
  assert property (max_output == (gt ? b : Q))
    else $error("max_output mismatch to (gt ? b : Q)");

  //========================
  // Targeted coverage
  //========================

  // Reset activity
  cover property (RST ##1 !RST);

  // Counter boundary and typical transitions
  cover property (disable iff (RST) $past(DIR) && ($past(Q)==16'hFFFF) |=> Q==16'h0000); // wrap up
  cover property (disable iff (RST) $past(DIR) && ($past(Q)==16'h0000) |=> Q==16'h0001); // inc from 0
  cover property (disable iff (RST) !$past(DIR) && ($past(Q)==16'h0001) |=> Q==16'h0000); // dec to 0

  // Comparator states
  cover property (lt);
  cover property (eq);
  cover property (gt);

  // max_value select paths
  cover property (gt && (max_output==b));
  cover property (!gt && (max_output==Q));

  // Direction toggling
  cover property (DIR ##1 !DIR);
  cover property (!DIR ##1 DIR);

endmodule

// Bind to the DUT top level
bind top_module top_module_sva sva_i (
  .CLK(CLK),
  .RST(RST),
  .DIR(DIR),
  .a(a),
  .b(b),
  .Q(Q),
  .lt(lt),
  .eq(eq),
  .gt(gt),
  .max_output(max_output)
);