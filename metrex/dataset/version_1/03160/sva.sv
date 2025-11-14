// SVA for shift_register_4bit
module shift_register_4bit_sva(
  input clk,
  input rst,
  input load,
  input [3:0] data_in,
  input shift,
  input [3:0] data_out
);

default clocking cb @(posedge clk); endclocking

// Async reset clears immediately and holds zero while asserted
assert property (@(negedge rst) ##0 (data_out == 4'b0));
assert property (@(posedge clk) !rst |-> (data_out == 4'b0));

// No X on output after each clock when out of reset
assert property (disable iff (!rst) 1'b1 |=> !$isunknown(data_out));

// Data_in must be known when loading
assert property (disable iff (!rst) load |-> !$isunknown(data_in));

// Load has priority and captures data_in on next cycle
assert property (disable iff (!rst) load |=> (data_out == $past(data_in)));

// Shift-left with zero fill when not loading
assert property (disable iff (!rst)
  (!load && shift) |=> (data_out == {$past(data_out[2:0]), 1'b0})
);

// Hold value when neither load nor shift
assert property (disable iff (!rst)
  (!load && !shift) |=> (data_out == $past(data_out))
);

// Coverage
cover property (@(negedge rst) 1'b1);
cover property (@(posedge rst) 1'b1);
cover property (disable iff (!rst) load);
cover property (disable iff (!rst) shift);
cover property (disable iff (!rst) (!load && !shift));
cover property (disable iff (!rst) (load && shift));      // priority scenario
cover property (disable iff (!rst) load ##1 shift);       // load then shift
cover property (disable iff (!rst) ((!load && shift)[*4]) ##1 (data_out == 4'b0));

endmodule

// Bind into DUT
bind shift_register_4bit shift_register_4bit_sva sva_i(
  .clk(clk),
  .rst(rst),
  .load(load),
  .data_in(data_in),
  .shift(shift),
  .data_out(data_out)
);