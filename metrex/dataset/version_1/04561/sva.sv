// SVA checker for top_module
module top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [7:0]  a,
  input logic [7:0]  b,
  input logic        select,
  input logic [7:0]  out,
  input logic [7:0]  sum1,
  input logic [7:0]  sum2
);

  default clocking cb @(posedge clk); endclocking

  // Basic mux correctness
  a_mux:         assert property (out == (select ? sum1 : sum2));

  // Synchronous reset clears regs and out by next cycle
  a_reset:       assert property (reset |=> (sum1==8'h00 && sum2==8'h00 && out==8'h00));

  // Update/hold behavior per select
  a_sum1_upd:    assert property (disable iff (reset)  select  |=> sum1 == $past(a + b));
  a_sum2_hold:   assert property (disable iff (reset)  select  |=> $stable(sum2));

  a_sum2_upd:    assert property (disable iff (reset) !select  |=> sum2 == $past(a + b));
  a_sum1_hold:   assert property (disable iff (reset) !select  |=> $stable(sum1));

  // No X on key outputs when not in reset
  a_no_x:        assert property (disable iff (reset) !$isunknown({out,sum1,sum2,select}));

  // Coverage
  c_reset:       cover  property (reset ##1 !reset);
  c_sel1:        cover  property (disable iff (reset)  select);
  c_sel0:        cover  property (disable iff (reset) !select);
  c_toggle_01:   cover  property (disable iff (reset) !select ##1 select);
  c_toggle_10:   cover  property (disable iff (reset)  select ##1 !select);
  // Overflow/wrap opportunities on each path
  c_wrap1:       cover  property (disable iff (reset)  select && ({1'b0,a}+{1'b0,b})[8]);
  c_wrap0:       cover  property (disable iff (reset) !select && ({1'b0,a}+{1'b0,b})[8]);

endmodule

// Bind into DUT
bind top_module top_module_sva sva_i (
  .clk(clk),
  .reset(reset),
  .a(a),
  .b(b),
  .select(select),
  .out(out),
  .sum1(sum1),
  .sum2(sum2)
);