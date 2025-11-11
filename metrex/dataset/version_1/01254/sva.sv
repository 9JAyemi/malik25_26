// SVA for majority_gate
// Bind this checker to the DUT instance(s).
module majority_gate_sva (
  input logic a,
  input logic b,
  input logic c,
  input logic reset,
  input logic out_assign,
  input logic out_alwaysblock
);

  function automatic logic maj3 (logic aa, logic bb, logic cc);
    return (aa & bb) | (aa & cc) | (bb & cc);
  endfunction

  // Sample on any input or reset edge; use ##0 to avoid race with combinational updates
  default clocking cb @(
    posedge a or negedge a or
    posedge b or negedge b or
    posedge c or negedge c or
    posedge reset or negedge reset
  ); endclocking

  // Inputs known -> outputs must be known
  assert property (disable iff ($isunknown({a,b,c,reset}))
                   1'b1 |-> ##0 !$isunknown({out_assign,out_alwaysblock}));

  // out_assign must implement majority function
  assert property (disable iff ($isunknown({a,b,c,reset}))
                   1'b1 |-> ##0 (out_assign == maj3(a,b,c)));

  // out_alwaysblock: reset dominates, else majority
  assert property (disable iff ($isunknown({a,b,c,reset}))
                   1'b1 |-> ##0 (out_alwaysblock == (reset ? 1'b0 : maj3(a,b,c))));

  // When not in reset, both outputs must agree
  assert property (disable iff ($isunknown({a,b,c,reset}))
                   !reset |-> ##0 (out_assign == out_alwaysblock));

  // Functional coverage of all input combinations (post-update)
  cover property (##0 {!$isunknown({a,b,c})} && ({a,b,c}==3'b000));
  cover property (##0 {!$isunknown({a,b,c})} && ({a,b,c}==3'b001));
  cover property (##0 {!$isunknown({a,b,c})} && ({a,b,c}==3'b010));
  cover property (##0 {!$isunknown({a,b,c})} && ({a,b,c}==3'b011));
  cover property (##0 {!$isunknown({a,b,c})} && ({a,b,c}==3'b100));
  cover property (##0 {!$isunknown({a,b,c})} && ({a,b,c}==3'b101));
  cover property (##0 {!$isunknown({a,b,c})} && ({a,b,c}==3'b110));
  cover property (##0 {!$isunknown({a,b,c})} && ({a,b,c}==3'b111));

  // Output toggle coverage (no reset)
  cover property (##0 !reset && $rose(out_assign));
  cover property (##0 !reset && $fell(out_assign));

  // Reset-gating scenario: assign path can be 1 while alwaysblock is forced 0
  cover property (##0 reset && maj3(a,b,c) && out_assign && !out_alwaysblock);

  // Equivalence scenarios when not in reset
  cover property (##0 !reset && maj3(a,b,c) && out_assign && out_alwaysblock);
  cover property (##0 !reset && !maj3(a,b,c) && !out_assign && !out_alwaysblock);

endmodule

// Bind to the DUT
bind majority_gate majority_gate_sva sva (
  .a(a), .b(b), .c(c), .reset(reset),
  .out_assign(out_assign),
  .out_alwaysblock(out_alwaysblock)
);