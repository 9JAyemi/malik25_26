// SVA for mag_comparator_4bit
// Quality-focused, concise checks and coverage

module mag_comparator_4bit_sva (
  input logic        clk,
  input logic [3:0]  A, B,
  input logic [3:0]  A_reg, B_reg,
  input logic [2:0]  stage,
  input logic        LT
);

  default clocking cb @(posedge clk); endclocking
  default disable iff ($initstate);

  // State is only 0 or 1 and must toggle every cycle
  assert property (stage inside {3'd0,3'd1});
  assert property (stage==3'd0 |=> stage==3'd1);
  assert property (stage==3'd1 |=> stage==3'd0);

  // Registered capture of inputs occurs in stage 0 (one-cycle latency)
  assert property ($past(stage==3'd0) |-> (A_reg==$past(A) && B_reg==$past(B)));

  // A_reg/B_reg only change following a stage 0 cycle (never during stage 1)
  assert property (((A_reg!=$past(A_reg)) || (B_reg!=$past(B_reg))) |-> $past(stage==3'd0));

  // Functional correctness: LT reflects A<B of the sampled values after one cycle
  assert property ($past(stage==3'd0) |-> (LT == $past(A<B)));

  // LT updates only on stage 1 and is held during stage 0
  assert property ((LT != $past(LT)) |-> $past(stage==3'd1));
  assert property (stage==3'd0 |-> LT==$past(LT));

  // No X on LT after initialization
  assert property (!$isunknown(LT));

  // Coverage
  cover property (stage==3'd0 ##1 stage==3'd1 ##1 stage==3'd0);                // pipeline cadence
  cover property ($past(stage==3'd0) ##1 (LT==1  && $past(A<B)));              // LT=1 path
  cover property ($past(stage==3'd0) ##1 (LT==0  && $past(!(A<B)))) ;          // LT=0 path
  cover property ($past(stage==3'd0 && A==B)     ##1 (LT==0));                 // equal case
  cover property ($past(stage==3'd0 && A==4'h0 && B==4'hF) ##1 (LT==1));       // min<max
  cover property ($past(stage==3'd0 && A==4'hF && B==4'h0) ##1 (LT==0));       // max<!min

endmodule

bind mag_comparator_4bit mag_comparator_4bit_sva i_mag_comparator_4bit_sva (.*);