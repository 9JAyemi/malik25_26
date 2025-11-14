// SVA for shift_register
module shift_register_sva #(parameter int WIDTH = 8)
(
  input logic                clk,
  input logic                reset,
  input logic                load,
  input logic                shift,
  input logic [WIDTH-1:0]    data_in,
  input logic [WIDTH-1:0]    data_out
);

  default clocking cb @(posedge clk); endclocking

  // Parameter sanity
  initial assert (WIDTH >= 1) else $error("WIDTH must be >= 1");

  // X checks
  assert property (! $isunknown({reset, load, shift}));
  assert property (load |-> ! $isunknown(data_in));
  assert property (disable iff (reset) ! $isunknown(data_out));

  // Reset behavior (synchronous)
  assert property (reset |=> data_out == '0);

  // Load has priority over shift
  assert property ((!reset && load) |=> data_out == $past(data_in));

  // Shift left by 1 with zero fill when enabled and not loading
  assert property ((!reset && !load && shift) |=> data_out == ($past(data_out) << 1));

  // Hold when neither load nor shift
  assert property ((!reset && !load && !shift) |=> data_out == $past(data_out));

  // After WIDTH consecutive shifts (no load), output becomes zero
  assert property (disable iff (reset) ((shift && !load)[*WIDTH]) |=> data_out == '0);

  // Functional coverage
  cover property (reset ##1 !reset ##1 load ##1 !load ##1 shift);
  cover property (disable iff (reset) (load && shift));            // priority case exercised
  cover property (disable iff (reset) (!load && !shift));          // hold case
  cover property (disable iff (reset) (shift && !load)[*WIDTH]);   // long shift run to zero

endmodule

// Bind into DUT
bind shift_register shift_register_sva #(.WIDTH(width)) u_shift_register_sva (.*);