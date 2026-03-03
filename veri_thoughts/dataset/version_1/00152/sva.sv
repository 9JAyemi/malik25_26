// SVA for comparator — bind into DUT to check/cover pipeline, capture, compare, and outputs

module comparator_sva (
  input logic        clk,
  input logic [7:0]  A, B,
  input logic        EQ, GT,
  input logic [7:0]  A_reg, B_reg,
  input logic [2:0]  stage
);

  default clocking cb @(posedge clk); endclocking

  // $past guard
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // State validity and progression
  assert property (cb, ! $isunknown(stage) |-> stage inside {3'd0,3'd1,3'd2});
  assert property (cb, disable iff ($isunknown(stage)) (stage==3'd0) |=> stage==3'd1);
  assert property (cb, disable iff ($isunknown(stage)) (stage==3'd1) |=> stage==3'd2);
  assert property (cb, disable iff ($isunknown(stage)) (stage==3'd2) |=> stage==3'd0);

  // Register capture correctness (stage0 captures inputs for use in stage1)
  assert property (cb, disable iff (!past_valid || $isunknown(stage))
                   (stage==3'd0) |=> (stage==3'd1 && A_reg==$past(A) && B_reg==$past(B)));

  // A_reg/B_reg may only change when stage was 0
  assert property (cb, disable iff (!past_valid)
                   (A_reg != $past(A_reg)) |-> $past(stage==3'd0));
  assert property (cb, disable iff (!past_valid)
                   (B_reg != $past(B_reg)) |-> $past(stage==3'd0));

  // Outputs mapping: results appear one cycle after stage1 (during stage2 sample)
  assert property (cb, disable iff ($isunknown(stage))
                   (stage==3'd1) |=> ((A_reg==B_reg) -> ( EQ && !GT)) &&
                                      ((A_reg> B_reg) -> (!EQ &&  GT)) &&
                                      ((A_reg< B_reg) -> (!EQ && !GT)));

  // Outputs are 0 in stage0 and stage1; any nonzero only during stage2
  assert property (cb, disable iff ($isunknown(stage))
                   (stage inside {3'd0,3'd1}) |-> (!EQ && !GT));
  assert property (cb, disable iff ($isunknown(stage))
                   (EQ || GT) |-> stage==3'd2);

  // Outputs cleared after stage2
  assert property (cb, disable iff ($isunknown(stage)) (stage==3'd2) |=> (!EQ && !GT));

  // Output mutual exclusion and no X when stage known
  assert property (cb, !(EQ && GT));
  assert property (cb, ! $isunknown(stage) |-> ! $isunknown({EQ,GT}));

  // Output changes only due to stage1 or stage2 assignments
  assert property (cb, disable iff (!past_valid)
                   ((EQ!=$past(EQ)) || (GT!=$past(GT))) |-> $past(stage inside {3'd1,3'd2}));

  // One-cycle pulses on EQ/GT when they rise
  assert property (cb, disable iff (!past_valid) $rose(EQ) |-> $past(stage==3'd1) ##1 !EQ);
  assert property (cb, disable iff (!past_valid) $rose(GT) |-> $past(stage==3'd1) ##1 !GT);

  // Coverage
  cover property (cb (stage==3'd0) ##1 (stage==3'd1) ##1 (stage==3'd2) ##1 (stage==3'd0));
  cover property (cb (stage==3'd1 && A_reg==B_reg) ##1 (stage==3'd2 &&  EQ && !GT));
  cover property (cb (stage==3'd1 && A_reg> B_reg) ##1 (stage==3'd2 && !EQ &&  GT));
  cover property (cb (stage==3'd1 && A_reg< B_reg) ##1 (stage==3'd2 && !EQ && !GT));
  cover property (cb $rose(EQ));
  cover property (cb $rose(GT));

endmodule

// Bind into DUT (connects to internals A_reg/B_reg/stage)
bind comparator comparator_sva u_comparator_sva (.*);