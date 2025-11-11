// SVA for clkgate. Bind this to the DUT.
// Focus: functional equivalence, mode-specific behavior, sanity/X checks, concise coverage.

module clkgate_asserts (
  input logic clk_in,
  input logic test_mode,
  input logic clock_en,
  input logic FPGA_SOURCE, // unused by DUT; compile-time `ifdef is used instead
  input logic clk_out
);

  // Common: output low whenever clk_in is low
  assert property (@(posedge clk_in or negedge clk_in or posedge clock_en or negedge clock_en or posedge test_mode or negedge test_mode)
                   (clk_in===1'b0) |-> (clk_out===1'b0));

`ifdef FPGA_SOURCE
  // In FPGA build: clk_out must equal clk_in
  assert property (@(posedge clk_in or negedge clk_in or posedge clock_en or negedge clock_en or posedge test_mode or negedge test_mode)
                   !$isunknown(clk_in) |-> (clk_out == clk_in));

  // Any clk_out edge must coincide with a clk_in edge
  assert property (@(posedge clk_out or negedge clk_out) $changed(clk_in));

  // Coverage: see both clk_in edges propagate to clk_out
  cover property (@(posedge clk_in) clk_out==1'b1);
  cover property (@(negedge clk_in) clk_out==1'b0);

`else
  // ASIC build: clk_out == clk_in & (clock_en | test_mode)
  assert property (@(posedge clk_in or negedge clk_in or posedge clock_en or negedge clock_en or posedge test_mode or negedge test_mode)
                   !$isunknown({clk_in,clock_en,test_mode})
                   |-> (clk_out == (clk_in & (clock_en | test_mode))));

  // Mode-specific behavior
  assert property (@(posedge clk_in or negedge clk_in)
                   (test_mode && !$isunknown(clk_in)) |-> (clk_out == clk_in));
  assert property (@(posedge clk_in or negedge clk_in)
                   (!test_mode && !clock_en) |-> (clk_out==1'b0));
  assert property (@(posedge clk_in or negedge clk_in)
                   (!test_mode && clock_en && !$isunknown(clk_in)) |-> (clk_out==clk_in));

  // Output must be known when inputs are known
  assert property (@(posedge clk_in or negedge clk_in or posedge clock_en or negedge clock_en or posedge test_mode or negedge test_mode)
                   (!$isunknown({clk_in,clock_en,test_mode})) |-> !$isunknown(clk_out));

  // Coverage: gate off, then on, then off
  cover property (@(posedge clk_in)
                  (!test_mode && !clock_en && clk_out==1'b0)
                  ##1 (!test_mode &&  clock_en && clk_out==clk_in)
                  ##1 (!test_mode && !clock_en && clk_out==1'b0));

  // Coverage: test_mode overrides gating (clk_out follows clk)
  cover property (@(posedge clk_in) test_mode && (clk_out==clk_in));
  cover property (@(negedge clk_in) test_mode && (clk_out==clk_in));

  // Coverage: enable toggled while clk high (illustrates potential glitch window)
  cover property (@(posedge clock_en or negedge clock_en) (clk_in===1'b1));

`endif

endmodule

bind clkgate clkgate_asserts clkgate_asserts_i (
  .clk_in(clk_in),
  .test_mode(test_mode),
  .clock_en(clock_en),
  .FPGA_SOURCE(FPGA_SOURCE),
  .clk_out(clk_out)
);