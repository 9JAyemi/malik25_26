// SVA for shift_register
module shift_register_sva (
  input logic        clk,
  input logic        reset,
  input logic        load,
  input logic [7:0]  data_in,
  input logic [7:0]  data_out
);

default clocking cb @(posedge clk); endclocking

// Hold zero for entire duration of reset (async clear behavior)
property hold_zero_during_reset;
  disable iff (1'b0)
  !reset |-> (data_out == 8'h00) until_with reset;
endproperty
assert property (hold_zero_during_reset);

// Assertions active only when not in reset
default disable iff (!reset);

// Basic sanity
assert property (!$isunknown(reset));
assert property (!$isunknown(load));
assert property (!$isunknown(data_out));
assert property (load |-> !$isunknown(data_in));

// Load has priority: next cycle equals sampled data_in
assert property (load |=> data_out == $past(data_in));

// Rotate-left with wrap when not loading
assert property ((!load) |=> data_out == {$past(data_out[6:0]), $past(data_out[7])});

// Coverage
cover property (load);
cover property (!load);
cover property (load ##1 (!load && reset)[*8] ##1 (data_out == $past(data_out,8))); // 8-step full rotation returns to original
cover property ((!load && $past(data_out[7])) |=> data_out[0]); // MSB-to-LSB wrap observed

endmodule

// Bind into DUT
bind shift_register shift_register_sva sva_inst (
  .clk(clk),
  .reset(reset),
  .load(load),
  .data_in(data_in),
  .data_out(data_out)
);