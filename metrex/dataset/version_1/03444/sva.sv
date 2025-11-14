// SVA for mux4to1
module mux4to1_sva (
  input logic clk,
  input logic in0, in1, in2, in3,
  input logic sel0, sel1,
  input logic out
);

  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Basic sanity: select must be known at sampling time
  assert property (past_valid |-> !$isunknown({sel1,sel0}));

  // Functional correctness: 1-cycle registered latency mapping
  assert property (past_valid && $past({sel1,sel0})==2'b00 |-> out === $past(in0));
  assert property (past_valid && $past({sel1,sel0})==2'b01 |-> out === $past(in1));
  assert property (past_valid && $past({sel1,sel0})==2'b10 |-> out === $past(in2));
  assert property (past_valid && $past({sel1,sel0})==2'b11 |-> out === $past(in3));

  // Out must be known if prior select and all inputs were known
  assert property (past_valid &&
                   !$isunknown($past({sel1,sel0,in0,in1,in2,in3}))
                   |-> !$isunknown(out));

  // Coverage: exercise all selections with both data values
  cover property (past_valid && $past({sel1,sel0})==2'b00 && $past(in0)==0 && out==0);
  cover property (past_valid && $past({sel1,sel0})==2'b00 && $past(in0)==1 && out==1);

  cover property (past_valid && $past({sel1,sel0})==2'b01 && $past(in1)==0 && out==0);
  cover property (past_valid && $past({sel1,sel0})==2'b01 && $past(in1)==1 && out==1);

  cover property (past_valid && $past({sel1,sel0})==2'b10 && $past(in2)==0 && out==0);
  cover property (past_valid && $past({sel1,sel0})==2'b10 && $past(in2)==1 && out==1);

  cover property (past_valid && $past({sel1,sel0})==2'b11 && $past(in3)==0 && out==0);
  cover property (past_valid && $past({sel1,sel0})==2'b11 && $past(in3)==1 && out==1);

endmodule

bind mux4to1 mux4to1_sva u_mux4to1_sva (.*);