// SVA for module1 and module2 (bind to all instances)

module module1_sva (
  input logic        clk,
  input logic        reset,
  input logic [7:0]  d,
  input logic [7:0]  d_r,
  input logic [7:0]  q1_r,
  input logic [7:0]  q1_reversed,
  input logic [7:0]  q1
);

  function automatic logic [7:0] reverse8 (input logic [7:0] x);
    return {x[0],x[1],x[2],x[3],x[4],x[5],x[6],x[7]};
  endfunction

  default clocking cb @(negedge clk); endclocking

  // Reset effects (synchronous to negedge)
  assert property (reset |=> (d_r==8'h00 && q1_r==8'h00 && q1_reversed==8'h00 && q1==8'h00));

  // Normal operation (previous cycle not in reset)
  assert property ((!reset && !$past(reset,1,1'b1)) |-> (d_r == $past(d,1,'0)));
  assert property ((!reset && !$past(reset,1,1'b1)) |-> (q1_r == {$past(q1_r,1,'0)[6:0], $past(d_r,1,'0)[7]}));
  assert property ((!reset && !$past(reset,1,1'b1)) |-> (q1_reversed == reverse8($past(q1_r,1,'0))));
  // Output equals reversed prior q1_r
  assert property ((!reset && !$past(reset,1,1'b1)) |-> (q1 == reverse8($past(q1_r,1,'0))));

  // No X/Z after reset deasserted
  assert property (disable iff (reset) !$isunknown({d_r,q1_r,q1_reversed,q1}));

  // Internal regs update only on negedge (stable on posedge)
  assert property (@(posedge clk) $stable({d_r,q1_r,q1_reversed}));

  // Coverage
  cover property (reset ##1 !reset);
  cover property ((!reset && !$past(reset,1,1'b1)) && (q1_r == {$past(q1_r,1,'0)[6:0], $past(d_r,1,'0)[7]}));
  cover property ((!reset && !$past(reset,1,1'b1)) && (q1 == reverse8($past(q1_r,1,'0))) && (q1!=8'h00) && (q1!=8'hFF));

endmodule


module module2_sva (
  input logic        clk,
  input logic        reset,
  input logic [7:0]  in,
  input logic [7:0]  in_r,
  input logic [7:0]  q2_r,
  input logic [7:0]  q2
);

  default clocking cb @(negedge clk); endclocking

  // Reset effects (synchronous to negedge)
  assert property (reset |=> (in_r==8'h00 && q2_r==8'h00 && q2==8'h00));

  // Normal operation (previous cycle not in reset)
  assert property ((!reset && !$past(reset,1,1'b1)) |-> (in_r == $past(in,1,'0)));
  assert property ((!reset && !$past(reset,1,1'b1)) |-> (q2_r == {$past(q2_r,1,'0)[6:0], $past(in_r,1,'0)[7]}));
  // Output equals prior post-update q2_r expressed from past operands
  assert property ((!reset && !$past(reset,1,1'b1)) |-> (q2 == {$past(q2_r,1,'0)[6:0], $past(in_r,1,'0)[7]}));

  // No X/Z after reset deasserted
  assert property (disable iff (reset) !$isunknown({in_r,q2_r,q2}));

  // Internal regs update only on negedge (stable on posedge)
  assert property (@(posedge clk) $stable({in_r,q2_r}));

  // Coverage
  cover property (reset ##1 !reset);
  cover property ((!reset && !$past(reset,1,1'b1)) && (q2_r == {$past(q2_r,1,'0)[6:0], $past(in_r,1,'0)[7]}));
  cover property ((!reset && !$past(reset,1,1'b1)) && (q2 == {$past(q2_r,1,'0)[6:0], $past(in_r,1,'0)[7]}) && (q2!=8'h00) && (q2!=8'hFF));

endmodule


// Bind to all instances
bind module1 module1_sva m1_sva (
  .clk(clk),
  .reset(reset),
  .d(d),
  .d_r(d_r),
  .q1_r(q1_r),
  .q1_reversed(q1_reversed),
  .q1(q1)
);

bind module2 module2_sva m2_sva (
  .clk(clk),
  .reset(reset),
  .in(in),
  .in_r(in_r),
  .q2_r(q2_r),
  .q2(q2)
);