// SVA for pipelined_nor_gate and the 3-stage top chain
// Concise, event-driven (no clock), checks final functionality and stage relations,
// and provides basic functional coverage.

////////////////////////////////////////////////////////////
// Per-instance checks for pipelined_nor_gate
////////////////////////////////////////////////////////////
module pipelined_nor_gate_sva (
  input a, input b,
  input pipe1, input pipe2,
  input out
);
  // Sample on any relevant signal change
  default clocking cb @(
    posedge a or negedge a or
    posedge b or negedge b or
    posedge pipe1 or negedge pipe1 or
    posedge pipe2 or negedge pipe2 or
    posedge out   or negedge out
  ); endclocking

  // No X/Z on key signals at observed point
  assert property (##0 !$isunknown({a,b,pipe1,pipe2,out}))
    else $error("X/Z detected in pipelined_nor_gate");

  // Stage relations and final function (at end-of-delta)
  assert property (##0 pipe1 == ~(a & b))
    else $error("pipe1 != ~(a & b)");
  assert property (##0 pipe2 == ~pipe1)
    else $error("pipe2 != ~pipe1");
  assert property (##0 out   == pipe2)
    else $error("out != pipe2");
  assert property (##0 out   == (a & b))
    else $error("Functional AND mismatch");

  // Functional coverage: all input combinations observed with correct out
  cover property (##0 ({a,b}==2'b00) && (out==1'b0));
  cover property (##0 ({a,b}==2'b01) && (out==1'b0));
  cover property (##0 ({a,b}==2'b10) && (out==1'b0));
  cover property (##0 ({a,b}==2'b11) && (out==1'b1));

  // Toggle coverage on each input
  cover property ($changed(a));
  cover property ($changed(b));
endmodule

bind pipelined_nor_gate pipelined_nor_gate_sva
  u_pipelined_nor_gate_sva(.a(a), .b(b), .pipe1(pipe1), .pipe2(pipe2), .out(out));


////////////////////////////////////////////////////////////
// Top-level chain checks
////////////////////////////////////////////////////////////
module top_module_sva (
  input a, input b,
  input pipe1, input pipe2,
  input out
);
  default clocking cb @(
    posedge a or negedge a or
    posedge b or negedge b or
    posedge pipe1 or negedge pipe1 or
    posedge pipe2 or negedge pipe2 or
    posedge out   or negedge out
  ); endclocking

  // No X/Z at the chain taps
  assert property (##0 !$isunknown({a,b,pipe1,pipe2,out}))
    else $error("X/Z detected in top_module chain");

  // Chain function reduces to a & b
  assert property (##0 out == (a & b))
    else $error("top_module out != a & b");

  // Stage-to-stage equivalence in the replicated AND chain
  assert property (##0 pipe2 == pipe1)
    else $error("Stage g2 mismatch: pipe2 != pipe1");
  assert property (##0 out   == pipe2)
    else $error("Stage g3 mismatch: out != pipe2");

  // Coverage: all input combos at top seen with correct out
  cover property (##0 ({a,b,out}==3'b000));
  cover property (##0 ({a,b,out}==3'b010));
  cover property (##0 ({a,b,out}==3'b100));
  cover property (##0 ({a,b,out}==3'b111));

  // Propagation covers for rising events when the other input is 1
  cover property (($rose(a) && b) ##0 out);
  cover property (($rose(b) && a) ##0 out);
endmodule

bind top_module top_module_sva
  u_top_module_sva(.a(a), .b(b), .pipe1(pipe1), .pipe2(pipe2), .out(out));