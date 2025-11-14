// SVA for POR. Bind to the POR instance to access internal counter.
module por_sva #(parameter int unsigned COUNT_MAX = 24'd100000)
(
  input logic clk,
  input logic vdd,
  input logic rst,
  input logic [23:0] counter
);

  default clocking cb @(posedge clk); endclocking

  // 1) Power removed: next cycle rst=1, counter=0; hold while vdd==0
  assert property (!vdd |=> (rst && counter==0));
  assert property (!vdd && $past(!vdd) |-> (rst && counter==0));

  // 2) Counting while powered: increment until COUNT_MAX, then saturate and deassert rst
  assert property (vdd && counter < COUNT_MAX |-> ##1 (counter == $past(counter)+1 && rst));
  assert property (vdd && counter == COUNT_MAX |-> ##1 (counter == COUNT_MAX && !rst));

  // 3) Safety: rst low only at COUNT_MAX with vdd high
  assert property (!rst |-> (vdd && counter==COUNT_MAX));

  // 4) Counter never exceeds COUNT_MAX (ignore uninitialized X)
  assert property (disable iff ($isunknown(counter)) counter <= COUNT_MAX);

  // 5) Release timing after power-up: hold rst high COUNT_MAX cycles, then deassert
  sequence vdd_rise; $rose(vdd); endsequence
  assert property (vdd_rise |-> (vdd && rst)[*COUNT_MAX] ##1 (!rst && counter==COUNT_MAX));

  // Coverage
  cover property ($fell(vdd) ##1 $rose(vdd) ##[COUNT_MAX] (!rst && counter==COUNT_MAX));
  cover property ($rose(vdd) ##1 (vdd && rst)[*COUNT_MAX] ##1 (!rst && counter==COUNT_MAX));
  cover property (!rst ##1 !vdd ##1 (rst && counter==0)); // drop power after release and reassert

endmodule

// Bind into all POR instances (adjust instance/path as needed)
bind POR por_sva #(.COUNT_MAX(24'd100000))
  por_sva_i (.clk(clk), .vdd(vdd), .rst(rst), .counter(counter));