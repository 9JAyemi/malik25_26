// SVA for top_module
// Bind these assertions to the DUT; accesses internal regs via bind port connections.

module top_module_sva (
  input  logic        clk,
  input  logic        reset,          // active-low reset in DUT (0 = reset)
  input  logic [3:0]  load_value,     // unused by DUT, kept for completeness
  input  logic [3:0]  shift_value,
  input  logic        up_down,
  input  logic        shift_dir,
  input  logic [3:0]  RESULT,
  input  logic [3:0]  counter,
  input  logic [3:0]  shifted_value,
  input  logic [1:0]  select
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset); // disable assertions while reset is asserted (active-low)

  // Async reset drives regs and RESULT to 0 immediately on negedge reset
  assert property (@(negedge reset)
                   counter==4'h0 && shifted_value==4'h0 && select==2'b00 && RESULT==4'h0);

  // Counter next-state: +/-1 with wrap (use previous-cycle up_down)
  assert property ($past(reset) |-> counter == ($past(counter) + ($past(up_down) ? 4'd1 : 4'hF)));

  // Select next-state: mapping of shift_dir (previous cycle)
  assert property ($past(reset) |-> select == ($past(shift_dir) ? 2'b10 : 2'b01));

  // Select legality (no 00/11) once out of reset
  assert property (select inside {2'b01,2'b10});

  // Shifted_value next-state uses previous-cycle select and shift_value
  assert property ($past(reset) |->
                   ( ($past(select)==2'b01 && shifted_value == {$past(shift_value)[2:0],1'b0}) ||
                     ($past(select)==2'b10 && shifted_value == {1'b0,$past(shift_value)[3:1]}) ||
                     (($past(select)!=2'b01 && $past(select)!=2'b10) && shifted_value == $past(shift_value)) ));

  // RESULT is correct mux of current regs
  assert property (RESULT == ((select==2'b00) ? counter : shifted_value));

  // In normal operation, RESULT must always be shifted_value (select never 00)
  assert property (RESULT == shifted_value);

  // No X propagation once out of reset
  assert property (!$isunknown({counter, shifted_value, select, RESULT}));

  // First cycle after reset release: RESULT reflects unshifted previous shift_value
  assert property (($past(!reset) && reset) |-> RESULT == $past(shift_value));

  // Coverage

  // See both select encodings
  cover property (select==2'b01);
  cover property (select==2'b10);

  // Counter wrap-around in both directions
  cover property ($past(reset) && $past(up_down)  && $past(counter)==4'hF && counter==4'h0);
  cover property ($past(reset) && !$past(up_down) && $past(counter)==4'h0 && counter==4'hF);

  // Exercise both shift behaviors
  cover property ($past(reset) && $past(select)==2'b01 &&
                  shifted_value == {$past(shift_value)[2:0],1'b0});
  cover property ($past(reset) && $past(select)==2'b10 &&
                  shifted_value == {1'b0,$past(shift_value)[3:1]});

  // Hit the counter path during reset (select==00, RESULT==0)
  cover property (@(negedge reset) 1);

endmodule

// Bind into the DUT
bind top_module top_module_sva i_top_module_sva (
  .clk(clk),
  .reset(reset),
  .load_value(load_value),
  .shift_value(shift_value),
  .up_down(up_down),
  .shift_dir(shift_dir),
  .RESULT(RESULT),
  .counter(counter),
  .shifted_value(shifted_value),
  .select(select)
);