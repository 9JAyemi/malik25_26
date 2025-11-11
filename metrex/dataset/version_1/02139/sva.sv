// SVA for four_input_or_gate
// Bind this file to the DUT to check functional correctness and provide coverage.

module four_input_or_gate_sva (
  input logic X,
  input logic A, B, C, D,
  input logic VPWR, VGND, VPB, VNB
);

  // Sample on any relevant edge
  default clocking cb @(
      posedge A or negedge A or
      posedge B or negedge B or
      posedge C or negedge C or
      posedge D or negedge D or
      posedge VPWR or negedge VPWR or
      posedge VGND or negedge VGND or
      posedge VPB  or negedge VPB  or
      posedge VNB  or negedge VNB
  ); endclocking

  // Power-good definition
  wire power_good = (VPWR===1'b1 && VGND===1'b0 && VPB===1'b1 && VNB===1'b0);

  // Disable checks when power is not good
  default disable iff (!power_good);

  // Functional correctness (allow delta-cycle settle)
  assert property (1'b1 |-> ##0 (X === (A | B | C | D)))
    else $error("four_input_or_gate: X != A|B|C|D under power_good");

  // X must be known when inputs are known
  assert property (( !$isunknown({A,B,C,D}) ) |-> ##0 ( !$isunknown(X) ))
    else $error("four_input_or_gate: X is X/Z while inputs are known under power_good");

  // Output can change only if some input changed
  assert property ( $changed(X) |-> ($changed(A) or $changed(B) or $changed(C) or $changed(D)) )
    else $error("four_input_or_gate: X changed without any input change under power_good");

  // Single-input control: rising edge makes X=1 if others are 0
  assert property ( $rose(A) && !B && !C && !D |-> ##0 (X==1) )
    else $error("four_input_or_gate: A rise (others 0) did not set X");
  assert property ( $rose(B) && !A && !C && !D |-> ##0 (X==1) )
    else $error("four_input_or_gate: B rise (others 0) did not set X");
  assert property ( $rose(C) && !A && !B && !D |-> ##0 (X==1) )
    else $error("four_input_or_gate: C rise (others 0) did not set X");
  assert property ( $rose(D) && !A && !B && !C |-> ##0 (X==1) )
    else $error("four_input_or_gate: D rise (others 0) did not set X");

  // Single-input control: falling edge clears X if it was the only 1
  assert property ( $fell(A) && !B && !C && !D |-> ##0 (X==0) )
    else $error("four_input_or_gate: A fall (others 0) did not clear X");
  assert property ( $fell(B) && !A && !C && !D |-> ##0 (X==0) )
    else $error("four_input_or_gate: B fall (others 0) did not clear X");
  assert property ( $fell(C) && !A && !B && !D |-> ##0 (X==0) )
    else $error("four_input_or_gate: C fall (others 0) did not clear X");
  assert property ( $fell(D) && !A && !B && !C |-> ##0 (X==0) )
    else $error("four_input_or_gate: D fall (others 0) did not clear X");

  // Coverage: observe all 16 input combinations and X under power_good
  covergroup cg_inputs @(
      posedge A or negedge A or
      posedge B or negedge B or
      posedge C or negedge C or
      posedge D or negedge D
  );
    option.per_instance = 1;
    cp_inputs: coverpoint {A,B,C,D} iff (power_good) { bins all_vals[] = {[0:15]}; }
    cp_x     : coverpoint X           iff (power_good) { bins low={0}; bins high={1}; }
    x_vs_in  : cross cp_inputs, cp_x;
  endgroup
  cg_inputs cg_i = new();

  // Coverage: power_good observed
  cover property (power_good);

endmodule

// Bind into the DUT
bind four_input_or_gate four_input_or_gate_sva sva (
  .X(X), .A(A), .B(B), .C(C), .D(D),
  .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);