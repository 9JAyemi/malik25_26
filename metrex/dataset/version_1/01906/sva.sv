// SVA for clock_gate: concise, high-quality functional checks + coverage

`define CG_EVT posedge clk or negedge clk or posedge en or negedge en or posedge te or negedge te

module clock_gate_sva (
  input logic clk,
  input logic en,
  input logic te,
  input logic en_clk
);

  // Core functional equivalence (when signals are known)
  assert property (@(`CG_EVT)
    !$isunknown({clk,en,te,en_clk}) |-> (en_clk == (clk & en & te))
  );

  // No X on output when inputs are known
  assert property (@(`CG_EVT)
    !$isunknown({clk,en,te}) |-> !$isunknown(en_clk)
  );

  // Basic safety invariants
  assert property (@(`CG_EVT) en_clk |-> clk);        // en_clk high implies clk high
  assert property (@(`CG_EVT) en_clk |-> (en && te)); // en_clk high implies both enables high
  assert property (@(`CG_EVT) (!(en && te)) |-> (en_clk == 1'b0)); // disabled forces low

  // Edge-accurate pass-through when enabled
  assert property (@(posedge clk)  (en && te) |-> $rose(en_clk));
  assert property (@(negedge clk)  (en && te) |-> $fell(en_clk));

  // Immediate response to (test) enable level while clk is high
  assert property (@(posedge en) (te && clk) |-> en_clk);
  assert property (@(posedge te) (en && clk) |-> en_clk);

  // Immediate drop on disable of either control
  assert property (@(negedge en or negedge te) en_clk == 1'b0);

  // Functional coverage
  cover property (@(posedge clk)  (en && te) && $rose(clk) && $rose(en_clk)); // pass rising
  cover property (@(negedge clk)  (en && te) && $fell(clk) && $fell(en_clk)); // pass falling
  cover property (@(posedge clk) (!(en && te)) && (en_clk == 1'b0));          // block while disabled
  cover property (@(posedge en) (te && clk) && en_clk);                        // enable while clk=1
  cover property (@(posedge te) (en && clk) && en_clk);                        // TE enable while clk=1
  cover property (@(negedge en) en_clk == 1'b0);                               // disable via en
  cover property (@(negedge te) en_clk == 1'b0);                               // disable via te
  cover property (@(`CG_EVT) !$isunknown({clk,en,te,en_clk}));                 // clean (no X) op window

endmodule

// Bind into the DUT
bind clock_gate clock_gate_sva cg_sva (
  .clk(clk),
  .en(en),
  .te(te),
  .en_clk(en_clk)
);