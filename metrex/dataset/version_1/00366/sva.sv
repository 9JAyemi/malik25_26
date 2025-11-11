// SVA for shift_register and top_module
// Concise, high-quality checks + key coverage

// Checker for shift_register
module shift_register_sva(
    input  logic        clk,
    input  logic        areset,
    input  logic        load,
    input  logic        ena,
    input  logic [3:0]  data,
    input  logic [3:0]  q,
    input  logic [3:0]  counter
);
  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset behavior: immediate and while-held
  assert property (@(posedge areset) (q==4'b0 && counter==4'b0));
  assert property (areset |-> (q==4'b0 && counter==4'b0));

  // Load dominates: next-cycle state reflects load
  assert property (disable iff (areset)
                   load |=> (q == $past(data) && counter == 4'd0));

  // Shift on ena when not loading: rotate-left with MSB to LSB, counter++
  assert property (disable iff (areset)
                   (!load && ena) |=> (q == {$past(q)[2:0], $past(q)[3]} &&
                                       counter == $past(counter) + 4'd1));

  // Hold when idle
  assert property (disable iff (areset)
                   (!load && !ena) |=> (q == $past(q) &&
                                        counter == $past(counter)));

  // Explicitly check load priority over ena
  assert property (disable iff (areset)
                   (load && ena) |=> (q == $past(data) && counter == 4'd0));

  // Counter wrap on increment from 0xF
  assert property (disable iff (areset)
                   ($past(counter)==4'hF && !load && ena) |=> (counter==4'h0));

  // Rotation closure in 4 shifts (no load/reset during window)
  assert property (disable iff (areset)
                   (ena && !load)[*4] |=> (q == $past(q,4)));

  // Coverage
  cover property (areset ##1 !areset);                            // reset pulse observed
  cover property (disable iff (areset) load);                     // load used
  cover property (disable iff (areset) (!load && ena));           // shift used
  cover property (disable iff (areset) (!load && !ena));          // idle used
  cover property (disable iff (areset)
                  load ##1 (ena && !load)[*3]);                   // load then shifts
  cover property (disable iff (areset)
                  (ena && !load)[*16] ##1 (counter==4'd0));       // counter wrap
endmodule

bind shift_register shift_register_sva
(
  .clk     (clk),
  .areset  (areset),
  .load    (load),
  .ena     (ena),
  .data    (data),
  .q       (q),
  .counter (counter)
);

// Checker for top_module (combinational mux/latch behavior)
module top_module_sva(
    input  logic        clk,
    input  logic        load,
    input  logic        ena,
    input  logic [3:0]  data,
    input  logic [3:0]  q,               // top_module.q
    input  logic [3:0]  shift_reg_out    // internal wire
);
  default clocking cb @(posedge clk); endclocking

  // Next-cycle top q reflects selected source (load has priority)
  assert property (load |=> (q == $past(data)));
  assert property ((!load && ena) |=> (q == $past(shift_reg_out)));
  assert property ((!load && !ena) |=> (q == $past(q)));
  assert property ((load && ena) |=> (q == $past(data))); // priority check

  // Coverage: exercise all mux paths and latch hold
  cover property (load ##1 (!load && ena) ##1 (!load && !ena));
  cover property ((!load && ena)[*4]); // repeated follow of shift_reg_out
endmodule

bind top_module top_module_sva
(
  .clk           (clk),
  .load          (load),
  .ena           (ena),
  .data          (data),
  .q             (q),
  .shift_reg_out (shift_reg_out)
);