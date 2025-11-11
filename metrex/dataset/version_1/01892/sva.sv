// SVA for top_module
// Concise, high-quality checks and coverage of load/shift behavior and q mirroring

`ifndef TOP_MODULE_SVA
`define TOP_MODULE_SVA

module top_module_sva (top_module dut);
  localparam int W = 100;

  default clocking cb @(posedge dut.clk); endclocking

  // Guard $past usage
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge dut.clk) past_valid <= 1'b1;

  // Control signals known
  assert property (cb !$isunknown({dut.load, dut.ena})));

  // q mirrors internal shift_reg (race-safe with ##0)
  assert property (@(posedge dut.clk) ##0 (dut.q === dut.shift_reg));

  // Load has priority: next q equals current data
  assert property (disable iff (!past_valid)
                   cb dut.load |=> (dut.q == $past(dut.data)));

  // Hold when no enables and no load
  assert property (disable iff (!past_valid)
                   cb (!dut.load && dut.ena == 2'b00) |=> (dut.q == $past(dut.q)));

  // Left rotate by 1 when ena==01 (and no load)
  assert property (disable iff (!past_valid)
                   cb (!dut.load && dut.ena == 2'b01)
                   |=> (dut.q == { $past(dut.q[W-2:0]), $past(dut.q[W-1]) }));

  // Right rotate by 1 when ena==10 (and no load)
  assert property (disable iff (!past_valid)
                   cb (!dut.load && dut.ena == 2'b10)
                   |=> (dut.q == { $past(dut.q[0]), $past(dut.q[W-1:1]) }));

  // Both enables set: last-assignment-wins => behaves like right rotate
  assert property (disable iff (!past_valid)
                   cb (!dut.load && dut.ena == 2'b11)
                   |=> (dut.q == { $past(dut.q[0]), $past(dut.q[W-1:1]) }));

  // Minimal, meaningful coverage
  cover property (disable iff (!past_valid) cb dut.load);
  cover property (disable iff (!past_valid) cb (!dut.load && dut.ena == 2'b00));
  cover property (disable iff (!past_valid) cb (!dut.load && dut.ena == 2'b01));
  cover property (disable iff (!past_valid) cb (!dut.load && dut.ena == 2'b10));
  cover property (disable iff (!past_valid) cb (!dut.load && dut.ena == 2'b11));

  // Cover wrap-around effects explicitly
  cover property (disable iff (!past_valid)
                  cb (!dut.load && dut.ena == 2'b01)
                  |=> (dut.q[0] == $past(dut.q[W-1])));
  cover property (disable iff (!past_valid)
                  cb (!dut.load && dut.ena == 2'b10)
                  |=> (dut.q[W-1] == $past(dut.q[0])));

endmodule

// Bind into all instances of top_module
bind top_module top_module_sva sva_top_module();

`endif