// SVA for top_module and the two shift-register modules.
// Concise, high-signal-coverage checks and a few targeted covers.

// ---------- top_module SVA ----------
module top_module_sva (
  input clk,
  input reset,
  input [1:0] d,
  input [2:0] shift_reg_async,
  input [1:0] shift_reg_sync,
  input [4:0] q
);
  default clocking cb @ (posedge clk); endclocking

  // Make $past reliable and keep most checks off during reset
  logic past_valid;
  always @(posedge clk or negedge reset)
    if (!reset) past_valid <= 1'b0; else past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Async reset must take effect immediately and hold at 0 while reset is low
  // Immediate effect on negedge reset
  assert property (@(negedge reset) ##0 (shift_reg_async == 3'b000))
    else $error("top_module: shift_reg_async not cleared immediately on async reset");

  // Held low across clocks while reset is asserted
  assert property (disable iff (1'b0) ( !reset |-> (shift_reg_async == 3'b000) ))
    else $error("top_module: shift_reg_async not held at 0 during reset");

  // Async 3b shift behavior when not in reset (note: 2-bit d causes truncation)
  // Expected next = {old[0], d[1], d[0]} due to width truncation of {old[1:0], d}
  assert property ( reset |-> ##0 (shift_reg_async ==
                                    { $past(shift_reg_async[0]), $past(d[1]), $past(d[0]) }) )
    else $error("top_module: async shifter update mismatch");

  // Sync 2b reset behavior and shift behavior
  assert property ( reset |-> ##0 (shift_reg_sync == 2'b00) )
    else $error("top_module: shift_reg_sync not cleared on sync reset");

  assert property ( !reset |-> ##0 (shift_reg_sync ==
                                    { $past(shift_reg_sync[0]), $past(d[1]) }) )
    else $error("top_module: sync shifter update mismatch");

  // Output mapping must always reflect concatenation of internals (sampled after NBA)
  assert property ( ##0 (q == {shift_reg_async, shift_reg_sync}) )
    else $error("top_module: q does not equal {shift_reg_async, shift_reg_sync}");

  // Optional sanity: no X on q when out of reset
  assert property ( reset |-> ##0 (!$isunknown(q)) )
    else $error("top_module: X/Z detected on q when out of reset");

  // Coverage
  cover property (@(negedge reset) 1'b1);                 // async reset asserted
  cover property ( reset ##1 !reset ##1 reset );          // reset toggle sequence
  cover property ( reset && $changed(shift_reg_async) );  // async shifter activity
  cover property ( !reset && $changed(shift_reg_sync) );  // sync shifter activity
endmodule

bind top_module top_module_sva top_module_sva_i (
  .clk(clk), .reset(reset), .d(d),
  .shift_reg_async(shift_reg_async),
  .shift_reg_sync(shift_reg_sync),
  .q(q)
);

// ---------- shift_register_async SVA ----------
module shift_register_async_sva (
  input clk,
  input reset,
  input d,
  input [2:0] q
);
  default clocking cb @ (posedge clk); endclocking

  logic past_valid;
  always @(posedge clk or negedge reset)
    if (!reset) past_valid <= 1'b0; else past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Immediate async clear and held-at-zero during reset
  assert property (@(negedge reset) ##0 (q == 3'b000))
    else $error("shift_register_async: q not cleared immediately on async reset");
  assert property (disable iff (1'b0) ( !reset |-> (q == 3'b000) ))
    else $error("shift_register_async: q not held at 0 during reset");

  // Shift behavior when out of reset
  assert property ( reset |-> ##0 (q == { $past(q[1:0]), $past(d) }) )
    else $error("shift_register_async: shift update mismatch");

  // Coverage
  cover property (@(negedge reset) 1'b1);
  cover property ( reset && $changed(q) );
endmodule

bind shift_register_async shift_register_async_sva sra_sva_i (
  .clk(clk), .reset(reset), .d(d), .q(q)
);

// ---------- shift_register_sync SVA ----------
module shift_register_sync_sva (
  input clk,
  input reset,
  input [1:0] d,
  input [1:0] q
);
  default clocking cb @ (posedge clk); endclocking

  logic past_valid;
  always @(posedge clk or negedge reset)
    if (!reset) past_valid <= 1'b0; else past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Sync reset and shift behavior
  assert property ( reset |-> ##0 (q == 2'b00) )
    else $error("shift_register_sync: q not cleared on sync reset");

  assert property ( !reset |-> ##0 (q == { $past(q[0]), $past(d[1]) }) )
    else $error("shift_register_sync: shift update mismatch");

  // Coverage
  cover property ( reset );                // exercised sync reset
  cover property ( !reset && $changed(q) );
endmodule

bind shift_register_sync shift_register_sync_sva srs_sva_i (
  .clk(clk), .reset(reset), .d(d), .q(q)
);