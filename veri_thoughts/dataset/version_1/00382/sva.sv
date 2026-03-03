Here’s a concise, high-quality SVA block you can place inside and_gate (guarded from synthesis). It checks functionality, internal connectivity/rails, and provides meaningful coverage.

`ifndef SYNTHESIS
  // Sample on any input edge
  default clocking comb_clk @(posedge A or negedge A or posedge B or negedge B); endclocking

  // Core functionality (4-state accurate)
  assert property (X === (A & B)) else $error("AND functional mismatch: X != A & B");

  // Internal connectivity
  assert property (A1 === A) else $error("Connectivity: A1 != A");
  assert property (B1 === B) else $error("Connectivity: B1 != B");

  // One-time rail/constant checks
  initial begin
    assert (A2   === 1'b1) else $error("A2 not 1");
    assert (C1   === 1'b0) else $error("C1 not 0");
    assert (VPWR === 1'b1) else $error("VPWR not 1");
    assert (VGND === 1'b0) else $error("VGND not 0");
    assert (VPB  === 1'b1) else $error("VPB not 1");
    assert (VNB  === 1'b0) else $error("VNB not 0");
  end

  // Truth-table dominance checks
  assert property (!A |-> X == 1'b0) else $error("0-dominance on A violated");
  assert property (!B |-> X == 1'b0) else $error("0-dominance on B violated");
  assert property (A && B |-> X == 1'b1) else $error("AND 1,1 case violated");

  // Output should only change when an input changes (no spurious glitches)
  assert property (@(posedge X or negedge X) $changed(A) or $changed(B))
    else $error("X changed without input change");

  // Functional coverage: all input combinations with expected X
  cover property (A==1'b0 && B==1'b0 && X==1'b0);
  cover property (A==1'b0 && B==1'b1 && X==1'b0);
  cover property (A==1'b1 && B==1'b0 && X==1'b0);
  cover property (A==1'b1 && B==1'b1 && X==1'b1);

  // Toggle coverage on X
  cover property (@(posedge X) 1);
  cover property (@(negedge X) 1);
`endif