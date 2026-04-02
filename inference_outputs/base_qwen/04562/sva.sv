module mux4to1_sva (
  input logic in0,
  input logic in1,
  input logic in2,
  input logic in3,
  input logic sel0,
  input logic sel1,
  output logic out
);
  // Sequential logic is not present, so all assertions will be clocked.
  // No reset signal is present, so no disable iff clause is needed.

  // Mux output must be one of the input signals based on the selection.
  mux_output_valid: assert property (
    @(posedge clk) $onehot0({sel0, sel1}) |-> (out == in0 || out == in1 || out == in2 || out == in3)
  ) else $error("Mux output is not one of the input signals.");

  // Mux output must be in0 when sel0 and sel1 are both 0.
  mux_output_in0: assert property (
    @(posedge clk) $rose($onehot0({sel0, sel1})) |-> (out == in0)
  ) else $error("Mux output is not in0 when sel0 and sel1 are both 0.");

  // Mux output must be in1 when sel0 is 1 and sel1 is 0.
  mux_output_in1: assert property (
    @(posedge clk) $rose(sel0) && $rose(~sel1) |-> (out == in1)
  ) else $error("Mux output is not in1 when sel0 is 1 and sel1 is 0.");

  // Mux output must be in2 when sel0 is 0 and sel1 is 1.
  mux_output_in2: assert property (
    @(posedge clk) $rose(~sel0) && $rose(sel1) |-> (out == in2)
  ) else $error("Mux output is not in2 when sel0 is 0 and sel1 is 1.");

  // Mux output must be in3 when sel0 and sel1 are both 1.
  mux_output_in3: assert property (
    @(posedge clk) $rose(sel0) && $rose(sel1) |-> (out == in3)
  ) else $error("Mux output is not in3 when sel0 and sel1 are both 1.");

endmodule