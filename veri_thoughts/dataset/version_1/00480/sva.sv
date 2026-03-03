// SVA bind file for adc_transformer
// Focus: constants, register capture, 2's-complement-like transform, X-checks, and key coverage

module adc_transformer_sva #(parameter int W=14) (
  input  logic              adc_clk,
  input  logic [W-1:0]      adc_dat_a_i,
  input  logic [W-1:0]      adc_dat_b_i,
  input  logic [W-1:0]      adc_dat_a_o,
  input  logic [W-1:0]      adc_dat_b_o,
  input  logic [1:0]        adc_clk_source,
  input  logic              adc_cdcs_o,
  input  logic              adc_rst_i,      // unused by DUT, but available to assertions
  input  logic [W-1:0]      adc_dat_a,      // internal regs from DUT scope
  input  logic [W-1:0]      adc_dat_b
);

  default clocking cb @(posedge adc_clk); endclocking

  bit past_valid = 0;
  always @(posedge adc_clk) past_valid <= 1'b1;

  // Constants must hold every cycle
  assert property (adc_cdcs_o == 1'b1)
    else $error("adc_cdcs_o must be constant 1");

  assert property (adc_clk_source == 2'b10)
    else $error("adc_clk_source must be constant 2'b10");

  // Registered capture of inputs (1-cycle latency)
  assert property (past_valid |-> adc_dat_a == $past(adc_dat_a_i))
    else $error("adc_dat_a should capture adc_dat_a_i on clk");

  assert property (past_valid |-> adc_dat_b == $past(adc_dat_b_i))
    else $error("adc_dat_b should capture adc_dat_b_i on clk");

  // Output is pure transform of registered data (combinational relationship)
  assert property (adc_dat_a_o == {adc_dat_a[W-1], ~adc_dat_a[W-2:0]})
    else $error("adc_dat_a_o must equal {MSB, ~LSBs} of adc_dat_a");

  assert property (adc_dat_b_o == {adc_dat_b[W-1], ~adc_dat_b[W-2:0]})
    else $error("adc_dat_b_o must equal {MSB, ~LSBs} of adc_dat_b");

  // Output equals 1-cycle transformed input (pipeline equivalence)
  assert property (past_valid |-> adc_dat_a_o == {$past(adc_dat_a_i[W-1]), ~($past(adc_dat_a_i[W-2:0]))})
    else $error("adc_dat_a_o != transformed $past(adc_dat_a_i)");

  assert property (past_valid |-> adc_dat_b_o == {$past(adc_dat_b_i[W-1]), ~($past(adc_dat_b_i[W-2:0]))})
    else $error("adc_dat_b_o != transformed $past(adc_dat_b_i)");

  // X/Z checks on observables
  assert property (!$isunknown({adc_dat_a_o, adc_dat_b_o, adc_cdcs_o, adc_clk_source})))
    else $error("Observed outputs/constants contain X/Z");

  // Minimal, meaningful coverage
  // Input activity and sign flips
  cover property (past_valid && $changed(adc_dat_a_i));
  cover property (past_valid && $changed(adc_dat_b_i));
  cover property (past_valid && $rose(adc_dat_a_i[W-1]));
  cover property (past_valid && $fell(adc_dat_a_i[W-1]));
  cover property (past_valid && $rose(adc_dat_b_i[W-1]));
  cover property (past_valid && $fell(adc_dat_b_i[W-1]));
  // Corner input patterns
  cover property (past_valid && (adc_dat_a_i == '0));
  cover property (past_valid && (&adc_dat_a_i)); // all ones
  cover property (past_valid && (adc_dat_b_i == '0));
  cover property (past_valid && (&adc_dat_b_i)); // all ones
  // Output activity observed
  cover property (past_valid && $changed(adc_dat_a_o));
  cover property (past_valid && $changed(adc_dat_b_o));

endmodule

bind adc_transformer adc_transformer_sva #(.W(14)) adc_transformer_sva_i (.*);