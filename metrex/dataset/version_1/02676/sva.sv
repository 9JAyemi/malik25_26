// SVA bind for inverter
module inverter_sva (
  input  logic A,
  input  logic Y,
  input  logic A_valid,
  input  logic A_low,
  input  logic A_high,
  input  logic VPWR,
  input  logic VGND
);

  // Power rails must be correct
  initial begin
    assert (VPWR === 1'b1) else $error("inverter: VPWR != 1");
    assert (VGND === 1'b0) else $error("inverter: VGND != 0");
  end

  // Core truth-table and X-propagation (combinational, race-safe)
  always @* begin
    assert (
      (A === 1'b0 && Y === 1'b1) ||
      (A === 1'b1 && Y === 1'b0) ||
      ((A !== 1'b0 && A !== 1'b1) && Y === 1'bx)
    ) else $error("inverter: Y must be ~A for valid A, X for invalid A");
  end

  // Internal signal correctness
  always @* begin
    assert (A_low  === (A === 1'b0)) else $error("inverter: A_low mismatch");
    assert (A_high === (A === 1'b1)) else $error("inverter: A_high mismatch");
    if (A === 1'b0 || A === 1'b1)
      assert (A_valid === 1'b1) else $error("inverter: A_valid must be 1 when A is 0/1");
    if (A !== 1'b0 && A !== 1'b1)
      assert (A_valid !== 1'b1) else $error("inverter: A_valid must not be 1 when A is X/Z");
  end

  // Simple concurrent checks and coverage on edges (use ##0 to avoid race)
  default clocking cb @(posedge A or negedge A); endclocking

  // When A is valid, Y has no unknowns and inverts A
  assert property ( (A === 1'b0 || A === 1'b1) |-> ##0 (Y === ~A && !$isunknown(Y)) );

  // Transition coverage
  cover property (negedge A ##0 (Y === 1'b1));
  cover property (posedge A ##0 (Y === 1'b0));

  // Invalid-input coverage: observe X on Y when A is invalid
  always @* cover (A !== 1'b0 && A !== 1'b1 && Y === 1'bx);

endmodule

bind inverter inverter_sva sva_i (
  .A      (A),
  .Y      (Y),
  .A_valid(A_valid),
  .A_low  (A_low),
  .A_high (A_high),
  .VPWR   (VPWR),
  .VGND   (VGND)
);