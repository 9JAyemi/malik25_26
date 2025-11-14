// SVA for up_down_counter
module up_down_counter_sva (
  input        clk,
  input        rst_n,
  input        up_down,
  input  [3:0] load_data,
  input  [3:0] count,
  input  [3:0] count_reg1,
  input  [3:0] count_reg2
);

  default clocking cb @(posedge clk); endclocking

  // Basic sanity: output never X
  assert property (!$isunknown(count)));

  // Async reset effect visible by next clk: internal regs cleared
  assert property (!rst_n |-> (count_reg1 == 4'h0 && count_reg2 == 4'h0));

  // Pipeline updates when out of reset
  assert property (disable iff (!rst_n)
                   $past(rst_n) |-> (count_reg1 == $past(count_reg2) &&
                                     count_reg2 == $past(count)));

  // Combinational next-value mapping
  assert property ((load_data != 4'h0) |-> (count == load_data));
  assert property ((load_data == 4'h0 && up_down)  |-> (count == (count_reg1 + 4'h1)));
  assert property ((load_data == 4'h0 && !up_down) |-> (count == (count_reg1 - 4'h1)));

  // Explicit wrap checks
  assert property ((load_data == 4'h0 && up_down  && count_reg1 == 4'hF) |-> (count == 4'h0));
  assert property ((load_data == 4'h0 && !up_down && count_reg1 == 4'h0) |-> (count == 4'hF));

  // Coverage
  cover property (disable iff (!rst_n) (load_data != 4'h0));                             // load occurs
  cover property (disable iff (!rst_n) (load_data == 4'h0 && up_down  && count_reg1 == 4'hF)); // inc wrap
  cover property (disable iff (!rst_n) (load_data == 4'h0 && !up_down && count_reg1 == 4'h0)); // dec wrap
  cover property (disable iff (!rst_n) (load_data == 4'h0 && up_down) ##1 (load_data == 4'h0 && !up_down)); // both modes seen

endmodule

// Bind into DUT (relies on matching signal names, including internals)
bind up_down_counter up_down_counter_sva sva_i (.*);