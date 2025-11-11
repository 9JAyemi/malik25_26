// SVA checker for clock_gate
module clock_gate_sva (
  input logic CLK,
  input logic EN,
  input logic TE,
  input logic ENCLK
);

  default clocking cb @(posedge CLK); endclocking

  // Core behavior: registered, same-cycle NBA update (##0), with 2-state 'if' semantics
  // if (EN && !TE) ENCLK<=1 else ENCLK<=0  => ENCLK = (EN===1'b1) && (TE===1'b0)
  property p_enclk_fn;
    1'b1 |-> ##0 (ENCLK == ((EN === 1'b1) && (TE === 1'b0)));
  endproperty
  assert property (p_enclk_fn);

  // TE override and enable-specific checks (redundant but explicit)
  assert property ( (TE === 1'b1) |-> ##0 (ENCLK == 1'b0) );
  assert property ( ((EN === 1'b1) && (TE === 1'b0)) |-> ##0 (ENCLK == 1'b1) );

  // Output is never X/Z after each clock update
  assert property ( ##0 !$isunknown(ENCLK) );

  // Coverage: all input combos at sampling edge
  cover property ( (EN === 1'b0) && (TE === 1'b0) );
  cover property ( (EN === 1'b0) && (TE === 1'b1) );
  cover property ( (EN === 1'b1) && (TE === 1'b0) );
  cover property ( (EN === 1'b1) && (TE === 1'b1) );

  // Coverage: output toggles (observe post-NBA value)
  cover property ( ##0 $rose(ENCLK) );
  cover property ( ##0 $fell(ENCLK) );

endmodule

// Bind into DUT
bind clock_gate clock_gate_sva u_clock_gate_sva (.*);