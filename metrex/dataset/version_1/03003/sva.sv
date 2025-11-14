// SVA checker for relojes
// Bind example:
// bind relojes relojes_sva sva(.CLK_IN1(CLK_IN1), .CLK_OUT1(CLK_OUT1), .CLK_OUT2(CLK_OUT2), .CLK_OUT3(CLK_OUT3), .CLK_OUT4(CLK_OUT4), .count1(count1), .count2(count2), .count3(count3), .count4(count4));

module relojes_sva (
  input logic        CLK_IN1,
  input logic        CLK_OUT1,
  input logic        CLK_OUT2,
  input logic        CLK_OUT3,
  input logic        CLK_OUT4,
  input logic [7:0]  count1,
  input logic [7:0]  count2,
  input logic [7:0]  count3,
  input logic [7:0]  count4
);

  default clocking cb @(posedge CLK_IN1); endclocking

  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge CLK_IN1) past_valid <= 1'b1;

  default disable iff (!past_valid);

  // Next-state functional correctness (captures last-assignment-wins semantics)
  assert property (count1 == (($past(count1)==8'd24) ? 8'd0 : ($past(count1)+8'd1)));

  assert property (count2 == (($past(count2)==8'd12) ? 8'd0 :
                              (($past(count1)==8'd24) ? ($past(count2)+8'd1) : $past(count2))));

  assert property (count3 == (($past(count3)==8'd6) ? 8'd0 :
                              (($past(count2)==8'd12) ? ($past(count3)+8'd1) : $past(count3))));

  assert property (count4 == (($past(count3)==8'd6) ? ($past(count4)+8'd1) : $past(count4)));

  // Output correctness
  assert property (CLK_OUT1 == count1[0]);
  assert property (CLK_OUT2 == count2[0]);
  assert property (CLK_OUT3 == count3[0]);
  assert property (CLK_OUT4 == count4[0]);

  // Output toggle expectations on increment vs reset events
  assert property (($past(count1)!=8'd24) |-> (CLK_OUT1 != $past(CLK_OUT1)));
  assert property (($past(count1)==8'd24) |-> (CLK_OUT1 == $past(CLK_OUT1)));

  assert property (($past(count1)==8'd24 && $past(count2)!=8'd12) |-> (CLK_OUT2 != $past(CLK_OUT2)));
  assert property (($past(count2)==8'd12) |-> (CLK_OUT2 == $past(CLK_OUT2)));

  assert property (($past(count2)==8'd12 && $past(count3)!=8'd6) |-> (CLK_OUT3 != $past(CLK_OUT3)));
  assert property (($past(count3)==8'd6) |-> (CLK_OUT3 == $past(CLK_OUT3)));

  assert property (($past(count3)==8'd6) |-> (CLK_OUT4 != $past(CLK_OUT4)));
  assert property (($past(count3)!=8'd6) |-> (CLK_OUT4 == $past(CLK_OUT4)));

  // Key coverage
  cover property ($past(count1)==8'd24 && count1==8'd0);
  cover property ($past(count2)==8'd12 && count2==8'd0);
  cover property ($past(count3)==8'd6  && count3==8'd0 && count4==$past(count4)+8'd1);

  // Full cascade alignment
  cover property ($past(count1)==8'd24 && $past(count2)==8'd12 && $past(count3)==8'd6
                  ##1 (count1==8'd0 && count2==8'd0 && count3==8'd0));

  // Output activity
  cover property ($changed(CLK_OUT1));
  cover property ($changed(CLK_OUT2));
  cover property ($changed(CLK_OUT3));
  cover property ($changed(CLK_OUT4));

endmodule