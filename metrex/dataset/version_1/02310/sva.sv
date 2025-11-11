// SVA for a23_multiply
module a23_multiply_sva (
  input  logic                 i_clk,
  input  logic                 i_fetch_stall,
  input  logic [31:0]          i_a_in,
  input  logic [31:0]          i_b_in,
  input  logic [1:0]           i_function,
  input  logic                 i_execute,
  input  logic [31:0]          o_out,
  input  logic [1:0]           o_flags,
  input  logic                 o_done,

  input  logic                 enable,
  input  logic                 accumulate,
  input  logic [33:0]          multiplier,
  input  logic [33:0]          multiplier_bar,
  input  logic [33:0]          sum,
  input  logic [33:0]          sum34_b,
  input  logic [32:0]          sum_acc1,

  input  logic [5:0]           count,
  input  logic [67:0]          product
);

  default clocking cb @(posedge i_clk); endclocking

  // Basic X/known checks
  assert property (cb !$isunknown({i_execute,i_fetch_stall,i_function,i_a_in,i_b_in}));
  assert property (cb !$isunknown({o_out,o_flags,o_done}));

  // Static combinational relationships
  assert property (cb enable     == i_function[0]);
  assert property (cb accumulate == i_function[1]);
  assert property (cb multiplier     == {2'd0, i_a_in});
  assert property (cb multiplier_bar == (~{2'd0,i_a_in} + 34'd1));
  assert property (cb sum       == product[67:34] + sum34_b);
  assert property (cb sum_acc1  == {1'b0,product[32:1]} + {1'b0,i_a_in});
  assert property (cb (product[1:0]==2'b01) |-> (sum34_b==multiplier));
  assert property (cb (product[1:0]==2'b10) |-> (sum34_b==multiplier_bar));
  assert property (cb (product[1:0]!=2'b01 && product[1:0]!=2'b10) |-> (sum34_b==34'd0));

  // Output wiring correctness
  assert property (cb o_out == product[32:1]);
  assert property (cb o_flags[1] == product[32]);
  assert property (cb o_flags[0] == (product[32:1]==32'd0));

  // Range/safety
  assert property (cb count <= 6'd35);

  // Hold behavior
  assert property (cb i_fetch_stall |=> (count==$past(count) && product==$past(product) && o_done==$past(o_done)));
  assert property (cb (!i_fetch_stall && !i_execute) |=> (count==$past(count) && product==$past(product) && o_done==$past(o_done)));

  // o_done semantics (updates only on active cycle)
  assert property (cb (!i_fetch_stall && i_execute) |=> o_done == ($past(count)==6'd31));
  assert property (cb (i_fetch_stall || !i_execute) |=> o_done == $past(o_done));

  // State transitions when active (!stall && execute)
  // Kick: load multiplicand/multiplier window and start counting
  assert property (cb (!i_fetch_stall && i_execute && count==6'd0 && enable)
                   |=> (count==6'd1 && product=={33'd0,1'b0,i_b_in,1'b0}));
  assert property (cb (!i_fetch_stall && i_execute && count==6'd0 && !enable)
                   |=> (count==6'd0 && product==$past(product)));

  // Core Booth steps (1..33): shift/add path
  assert property (cb (!i_fetch_stall && i_execute && (count inside {[6'd1:6'd33]}))
                   |=> (count==$past(count)+6'd1 &&
                        product=={ $past(sum[33]), $past(sum), $past(product[33:1]) }));

  // Count==34 terminal step when not accumulating: no product update, return to idle
  assert property (cb (!i_fetch_stall && i_execute && count==6'd34 && !accumulate)
                   |=> (count==6'd0 && product==$past(product)));

  // Count==34 accumulate step: inject acc1, go to 35
  assert property (cb (!i_fetch_stall && i_execute && count==6'd34 && accumulate)
                   |=> (count==6'd35 &&
                        product[0]    == 1'b0 &&
                        product[32:1] == $past(sum_acc1[31:0]) &&
                        product[64:33]== $past(product[64:33])));

  // Count==35 (only reachable if accumulate): no product update, return to idle
  assert property (cb (!i_fetch_stall && i_execute && count==6'd35 && accumulate)
                   |=> (count==6'd0 && product==$past(product)));

  // Coverage
  cover property (cb (!i_fetch_stall && i_execute && count==6'd0 && enable)
                     ##1 (count==6'd1)
                     ##[1:40] (count==6'd34 && !accumulate)
                     ##1 (count==6'd0));
  cover property (cb (!i_fetch_stall && i_execute && count==6'd0 && enable)
                     ##[1:34] (count==6'd34 && accumulate)
                     ##1 (count==6'd35)
                     ##1 (count==6'd0));
  cover property (cb (count inside {[6'd1:6'd33]} && product[1:0]==2'b01));
  cover property (cb (count inside {[6'd1:6'd33]} && product[1:0]==2'b10));
  cover property (cb (count inside {[6'd1:6'd33]} && (product[1:0]==2'b00 || product[1:0]==2'b11)));
  cover property (cb $rose(o_done));

endmodule

// Example bind (place in a testbench or a separate bind file)
// Binds into every instance of a23_multiply and connects internals
bind a23_multiply a23_multiply_sva u_a23_multiply_sva (
  .i_clk(i_clk),
  .i_fetch_stall(i_fetch_stall),
  .i_a_in(i_a_in),
  .i_b_in(i_b_in),
  .i_function(i_function),
  .i_execute(i_execute),
  .o_out(o_out),
  .o_flags(o_flags),
  .o_done(o_done),
  .enable(enable),
  .accumulate(accumulate),
  .multiplier(multiplier),
  .multiplier_bar(multiplier_bar),
  .sum(sum),
  .sum34_b(sum34_b),
  .sum_acc1(sum_acc1),
  .count(count),
  .product(product)
);