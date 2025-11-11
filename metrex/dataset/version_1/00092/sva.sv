// SVA for sampler: bind this module to the DUT instance
module sampler_sva #(parameter int DW=32, CW=24) (
  input  logic               clk,
  input  logic               rst,
  input  logic               extClock_mode,
  input  logic               wrDivider,
  input  logic [CW-1:0]      config_data,
  input  logic               sti_valid,
  input  logic [DW-1:0]      sti_data,
  input  logic               sto_valid,
  input  logic [DW-1:0]      sto_data,
  input  logic               ready50,
  input  logic [CW-1:0]      divider,
  input  logic [CW-1:0]      counter,
  input  logic               counter_zero
);

  default clocking cb @ (posedge clk); endclocking
  default disable iff (rst);

  // Basic sanity
  assert property (!$isunknown({sto_valid, ready50}))) else $error("Outputs X/Z");
  assert property (!$isunknown({extClock_mode, wrDivider, sti_valid}))) else $error("Ctrls X/Z");
  assert property (counter_zero == (counter == '0)) else $error("counter_zero mismatch");

  // sto_valid/sto_data behavior
  // Ext-clock pass-through (wrDivider suppresses valid only)
  assert property ($past(extClock_mode && !wrDivider) |->
                   (sto_valid == $past(sti_valid) && sto_data == $past(sti_data)));
  assert property ($past(extClock_mode && wrDivider) |->
                   (!sto_valid && (sto_data == $past(sti_data))));

  // Internal-clocked sampling
  assert property ($past(!extClock_mode && sti_valid && counter_zero && !wrDivider) |->
                   (sto_valid && (sto_data == $past(sti_data))));
  // No false valids
  assert property (sto_valid |->
                   $past(sti_valid && !wrDivider && (extClock_mode || counter_zero)));
  // One-cycle pulse when divider!=0
  assert property ($past(!extClock_mode && sti_valid && counter_zero && !wrDivider && (divider!='0)) |->
                   !sto_valid);
  // Hold data when not sampling (non-ext mode)
  assert property ($past(!extClock_mode && !wrDivider && !(sti_valid && counter_zero)) |->
                   $stable(sto_data));
  // Valid suppressed on write
  assert property ($past(wrDivider) |-> !sto_valid);

  // Counter/divider behavior
  assert property ($past(wrDivider) |->
                   (divider == $past(config_data) && counter == divider));
  assert property ($past(!wrDivider && sti_valid && counter_zero) |->
                   (counter == $past(divider)));
  assert property ($past(!wrDivider && sti_valid && !counter_zero) |->
                   (counter == $past(counter) - 1));
  assert property ($past(!wrDivider && !sti_valid) |->
                   (counter == $past(counter)));

  // ready50 behavior
  assert property ($past(wrDivider) |-> (ready50 == 1'b0));
  assert property ($past(!wrDivider && counter_zero) |-> (ready50 == 1'b1));
  assert property ($past(!wrDivider && !counter_zero && (counter == divider[CW-1:1])) |->
                   (ready50 == 1'b0));
  // Hold when no update condition
  assert property ($past(!(wrDivider || counter_zero || (counter == divider[CW-1:1]))) |->
                   (ready50 == $past(ready50)));

  // Corner: divider==0 implies continuous sampling in non-ext mode
  assert property ($past(!extClock_mode && !wrDivider && (divider=='0) && sti_valid) |->
                   sto_valid);

  // Coverage
  cover property ($rose(extClock_mode) ##1 sti_valid ##1 sto_valid);
  cover property ($fell(extClock_mode) ##1 (sti_valid && counter_zero) ##1 sto_valid);
  cover property (wrDivider ##1 (!wrDivider && counter!='0) ##[1:$] counter_zero ##1 ready50 ##[1:$] (counter == divider[CW-1:1]) ##1 !ready50);
  cover property (extClock_mode && wrDivider && sti_valid ##1 (!sto_valid && (sto_data == $past(sti_data))));
  cover property (wrDivider && (config_data=='0) ##1 (divider=='0 && counter=='0) ##1 ready50);

endmodule

// Example bind (put in a separate file or below your DUT)
// bind sampler sampler_sva #(.DW(DW), .CW(CW)) u_sva (.*);