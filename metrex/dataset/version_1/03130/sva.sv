// SVA for up_counter
module up_counter_sva(input logic CLK, CLR, input logic [3:0] Q);

  default clocking cb @(posedge CLK); endclocking

  // Functional correctness
  assert property (CLR |=> (Q == 4'h0));
  assert property ((!CLR && !$isunknown($past(Q))) |=> (Q == (($past(Q)+4'd1) & 4'hF)));
  assert property ((!CLR && !$isunknown($past(Q)) && $past(Q)==4'hF) |=> (Q==4'h0)); // explicit wrap

  // Knownness propagation (avoid X/Z once known)
  assert property ((!$isunknown($past(Q))) |=> (!$isunknown(Q)));

  // Coverage
  cover property (CLR);
  cover property ((!CLR && !$isunknown($past(Q))) |=> (Q == (($past(Q)+4'd1) & 4'hF)));
  cover property (CLR ##1 (!CLR[*16]) ##1 (Q==4'h0)); // 16-count cycle after a reset

endmodule

bind up_counter up_counter_sva u_sva (.*);