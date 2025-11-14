// SVA checker for and3
module and3_sva(input logic a,b,c,y, input logic and1_out,and2_out);
  // Structural correctness
  assert property (and1_out === (a & b));
  assert property (and2_out === (and1_out & c));
  assert property (y === (and2_out & and1_out));
  // End-to-end equivalence
  assert property (y === (a & b & c));
  // Sanity: y high implies all inputs high
  assert property (y |-> (a && b && c));
  // Known-propagation
  assert property (!$isunknown({a,b,c}) |-> !$isunknown({and1_out,and2_out,y}));
  // Y rises only when all contributors are 1
  assert property ($rose(y) |-> (a && b && c && and1_out && and2_out));

  // Functional coverage of all input minterms
  cover property ((a===1'b0)&&(b===1'b0)&&(c===1'b0)&&(y===1'b0));
  cover property ((a===1'b0)&&(b===1'b0)&&(c===1'b1)&&(y===1'b0));
  cover property ((a===1'b0)&&(b===1'b1)&&(c===1'b0)&&(y===1'b0));
  cover property ((a===1'b0)&&(b===1'b1)&&(c===1'b1)&&(y===1'b0));
  cover property ((a===1'b1)&&(b===1'b0)&&(c===1'b0)&&(y===1'b0));
  cover property ((a===1'b1)&&(b===1'b0)&&(c===1'b1)&&(y===1'b0));
  cover property ((a===1'b1)&&(b===1'b1)&&(c===1'b0)&&(y===1'b0));
  cover property ((a===1'b1)&&(b===1'b1)&&(c===1'b1)&&(y===1'b1));

  // Toggle coverage
  cover property ($rose(a)); cover property ($fell(a));
  cover property ($rose(b)); cover property ($fell(b));
  cover property ($rose(c)); cover property ($fell(c));
  cover property ($rose(y)); cover property ($fell(y));
endmodule

bind and3 and3_sva and3_chk(.a(a),.b(b),.c(c),.y(y),.and1_out(and1_out),.and2_out(and2_out));

// SVA checker for leaf and2 gates
module and2_sva(input logic a,b,y);
  assert property (y === (a & b));
  assert property (!$isunknown({a,b}) |-> !$isunknown(y));
  cover property ($rose(a)); cover property ($fell(a));
  cover property ($rose(b)); cover property ($fell(b));
  cover property ((a===1'b1)&&(b===1'b1)&&(y===1'b1));
endmodule

bind and2 and2_sva and2_chk(.*);