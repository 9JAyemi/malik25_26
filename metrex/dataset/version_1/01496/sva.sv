// SVA checker for top_module
module top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic        enable1,
  input logic        enable2,
  input logic [3:0]  q1,
  input logic [3:0]  q2,
  input logic [3:0]  final_output,
  input logic [3:0]  counter1,
  input logic [3:0]  counter2
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Basic consistency
  assert property (q1 == counter1);
  assert property (q2 == counter2);
  assert property (final_output == (q1 | q2));
  assert property (!$isunknown({enable1,enable2,q1,q2,final_output}));

  // Reset behavior (check on every clock while reset is high)
  assert property (@(posedge clk) reset |-> (counter1==4'h0 && counter2==4'h0
                                            && q1==4'h0 && q2==4'h0 && final_output==4'h0));

  // Functional: enable/priority and hold
  assert property (enable1 |=> (counter1 == $past(counter1)+4'd1
                             && counter2 == $past(counter2)));
  assert property ((!enable1 && enable2) |=> (counter2 == $past(counter2)+4'd1
                                           && counter1 == $past(counter1)));
  assert property ((!enable1 && !enable2) |=> (counter1 == $past(counter1)
                                            && counter2 == $past(counter2)));

  // Safety: never both counters increment in same cycle
  assert property (!((counter1 != $past(counter1)) && (counter2 != $past(counter2))));

  // Coverage
  cover property (enable1 ##1 (counter1 == $past(counter1)+4'd1));
  cover property ((!enable1 && enable2) ##1 (counter2 == $past(counter2)+4'd1));
  cover property ((enable1 && enable2) ##1 (counter1 == $past(counter1)+4'd1
                                         && counter2 == $past(counter2)));
  cover property ((counter1==4'hF && enable1) ##1 (counter1==4'h0));
  cover property ((!enable1 && enable2 && counter2==4'hF) ##1 (counter2==4'h0));
  cover property (final_output == 4'hF);
  cover property ($rose(reset) ##1 (counter1==4'h0 && counter2==4'h0 && final_output==4'h0));
endmodule

// Bind into DUT (accesses internal counters)
bind top_module top_module_sva top_module_sva_i (
  .clk(clk),
  .reset(reset),
  .enable1(enable1),
  .enable2(enable2),
  .q1(q1),
  .q2(q2),
  .final_output(final_output),
  .counter1(counter1),
  .counter2(counter2)
);