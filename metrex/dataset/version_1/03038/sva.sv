// SVA for dlatch_reset
// Bindable, concise, high-signal-coverage

module dlatch_reset_sva (
  input logic D,
  input logic RESET_B,
  input logic GATE,
  input logic CLK,
  input logic Q,
  input logic Q_N,
  // internal comb nets
  input logic AND1_out,
  input logic AND2_out,
  input logic OR1_out,
  input logic NOT1_out,
  input logic NOT2_out
);

  default clocking cb @(posedge CLK); endclocking

  // Core functional checks (flop-like behavior with async active-low reset)
  // On clk when not in reset, Q/Q_N reflect previous cycle D&GATE
  assert property (cb disable iff (!RESET_B)
    (Q   == $past(D & GATE) &&
     Q_N == ~($past(D & GATE)))
  );

  // Reset dominates: on negedge reset, outputs go to reset values immediately
  assert property (@(negedge RESET_B) (Q==1'b0 && Q_N==1'b1));

  // If clock rises while reset is low, still held in reset
  assert property (@(posedge CLK) (!RESET_B |-> (Q==1'b0 && Q_N==1'b1)));

  // Outputs are complements at update points
  assert property (cb                    (Q_N == ~Q));
  assert property (@(negedge RESET_B)    (Q_N == ~Q));

  // No X/Z on outputs when out of reset
  assert property (cb disable iff (!RESET_B) (! $isunknown({Q,Q_N})));

  // Check internal combinational nets’ definitions (continuously true)
  assert property (AND1_out == (GATE & CLK));
  assert property (AND2_out == (~GATE & CLK));
  assert property (OR1_out  == (AND1_out | ~RESET_B));
  assert property (NOT1_out == ~OR1_out);
  assert property (NOT2_out == ~AND2_out);

  // Minimal but meaningful coverage
  cover property (@(negedge RESET_B) 1);        // reset assertion seen
  cover property (@(posedge RESET_B) 1);        // reset deassertion seen
  cover property (cb disable iff (!RESET_B) (GATE &&  D)); // gate open, D=1 sampled
  cover property (cb disable iff (!RESET_B) (GATE && !D)); // gate open, D=0 sampled

endmodule

// Bind into the DUT (connects to internal nets too)
bind dlatch_reset dlatch_reset_sva sva_i (
  .D(D),
  .RESET_B(RESET_B),
  .GATE(GATE),
  .CLK(CLK),
  .Q(Q),
  .Q_N(Q_N),
  .AND1_out(AND1_out),
  .AND2_out(AND2_out),
  .OR1_out(OR1_out),
  .NOT1_out(NOT1_out),
  .NOT2_out(NOT2_out)
);