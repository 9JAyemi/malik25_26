// SVA checker for top_module
// Bind this file to the DUT
module top_module_sva (
  input logic              clk,
  input logic              reset,
  input logic [9:0]        d,
  input logic [9:0]        q,
  input logic [9:0]        count_out,
  input logic [19:0]       mult_out,
  input logic [3:0]        shift_sel,
  input logic [9:0]        binary_counter,
  input logic              select,
  input logic [9:0]        shift_reg [0:9]
);

  default clocking cb @(posedge clk); endclocking
  localparam int unsigned MAX = 10'h3FF;

  // Reset behavior
  assert property (@cb reset |=> (shift_sel==4'b0001 && binary_counter==10'b0 && select==1'b0 && mult_out==20'b0));

  // Ties
  assert property (@cb q == shift_reg[shift_sel]);
  assert property (@cb count_out == binary_counter);

  // Known after reset
  assert property (@cb disable iff (reset) !$isunknown({q,count_out,mult_out,select}));

  // Binary counter next-state
  assert property (@cb disable iff (reset) $past(binary_counter)!=MAX |-> binary_counter == $past(binary_counter)+1);
  assert property (@cb disable iff (reset) $past(binary_counter)==MAX |-> binary_counter == '0);

  // shift_sel next-state as coded, and range check
  assert property (@cb reset |=> shift_sel==4'b0001);
  assert property (@cb disable iff (reset) shift_sel == (($past(shift_sel)==4'b1000) ? 4'b0001 : ($past(shift_sel)+1)));
  assert property (@cb shift_sel < 10);

  // Shift-register write: selected entry updates to past d; others hold
  assert property (@cb disable iff (reset) shift_reg[$past(shift_sel)] == $past(d));
  genvar i;
  generate
    for (i=0; i<10; i++) begin : g_sh_no_touch_others
      assert property (@cb disable iff (reset) ($past(shift_sel) != i) |-> (shift_reg[i] == $past(shift_reg[i])));
    end
  endgenerate

  // Multiplier next-state (uses prior-cycle operands)
  assert property (@cb reset |=> mult_out=='0);
  assert property (@cb disable iff (reset) mult_out == ($past(shift_reg[$past(shift_sel)]) * $past(count_out)));

  // select control: set on MAX, sticky afterwards, changes only on reset or MAX
  assert property (@cb disable iff (reset) $past(binary_counter)==MAX |-> select==1'b1);
  assert property (@cb disable iff (reset) $past(select) |-> select);
  assert property (@cb (!$stable(select)) |-> (reset || $past(binary_counter)==MAX));

  // Covers
  cover property (@cb disable iff (reset) binary_counter==MAX ##1 binary_counter=='0);
  cover property (@cb disable iff (reset) $rose(select));
  cover property (@cb disable iff (reset) mult_out != 0);
  generate
    for (i=0; i<10; i++) begin : g_cover_each_idx
      cover property (@cb disable iff (reset) $past(shift_sel)==i);
    end
  endgenerate

endmodule

// Bind into DUT
bind top_module top_module_sva u_top_module_sva (
  .clk(clk),
  .reset(reset),
  .d(d),
  .q(q),
  .count_out(count_out),
  .mult_out(mult_out),
  .shift_sel(shift_sel),
  .binary_counter(binary_counter),
  .select(select),
  .shift_reg(shift_reg)
);