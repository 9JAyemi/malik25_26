// SystemVerilog Assertions for top_module and sub-blocks
// Focused, high-signal-coverage, concise
// Bind into DUT to avoid modifying RTL

module top_module_sva (
    input logic         clk,
    input logic         reset,
    input logic [3:0]   in,
    input logic [7:0]   sel,
    input logic [1:0]   ena,
    input logic         load,
    input logic         select,
    input logic [3:0]   q,

    // internal nets from top_module
    input logic [3:0]   barrel_shift_out,
    input logic [3:0]   mux_out,
    input logic [3:0]   or_out
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset behavior (synchronous)
  assert property (@(posedge clk) reset |-> (q == 4'b0 && barrel_shift_out == 4'b0));

  // q_reg update protocol: priority reset > load > ena!=0 > hold
  assert property (load |=> q == $past(in));                      // load wins over ena
  assert property (!load && (ena != 2'b00) |=> q == $past(or_out));
  assert property (!load && (ena == 2'b00) |=> q == $past(q));

  // No unknowns on key outputs after reset is released
  assert property (!$isunknown(q));
  assert property (!$isunknown(barrel_shift_out));
  // Guard mux_out knownness to only supported select encodings
  assert property ((select == 1'b0 || sel inside {8'h00,8'h01,8'hFE,8'hFF}) |-> !$isunknown(mux_out));

  // Barrel shifter functional check (registered)
  assert property (barrel_shift_out == ($past(in) << $past(sel[3:0])));
  // Stronger check when shift exceeds data width
  assert property ($past(sel[3:0]) >= 4 |-> barrel_shift_out == 4'b0);

  // Mux functional checks (given partial case implementation)
  // When select==0, top forces mux.sel=8'hFF, which maps to in_0
  assert property (select == 1'b0 |-> mux_out == barrel_shift_out);
  // Explicitly check the encodings implemented in mux_256to1
  assert property (select && (sel == 8'h00) |-> mux_out == barrel_shift_out);
  assert property (select && (sel == 8'hFF) |-> mux_out == barrel_shift_out);

  // For safety: disallow unsupported select encodings while select==1 (avoids latch/undefined behavior)
  assert property (select |-> sel inside {8'h00,8'h01,8'hFE,8'hFF});

  // OR gate combinational correctness
  assert property (@(posedge clk) or_out == (barrel_shift_out | mux_out));

  // Coverage: exercise key behaviors
  cover property (!reset ##1 load ##1 (!load && (ena != 0)));                 // load then enable
  cover property (!reset && (ena != 0) && !load);                              // enable path taken
  cover property (!reset && load);                                            // load path taken
  cover property (!reset && select == 0);                                     // forced FF select path
  cover property (!reset && select && sel == 8'h00);                          // explicit sel==00 path
  cover property (!reset && ($past(sel[3:0]) >= 4) ##1 (barrel_shift_out==0)); // wide shift -> zero

endmodule

bind top_module top_module_sva top_module_sva_i (.*);