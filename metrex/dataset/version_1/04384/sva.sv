// SVA for top_module and its internal nets
// Bind once per top_module instance
module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [7:0]  in_1,
  input  logic [7:0]  in_2,
  input  logic        select,
  input  logic [7:0]  sum_output,
  input  logic [7:0]  or_output,
  input  logic [7:0]  selected_input,
  input  logic [8:0]  sum
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Functional correctness
  assert property (selected_input == (select ? in_2 : in_1))
    else $error("MUX output mismatch");

  assert property (sum == {1'b0, selected_input} + {1'b0, in_2})
    else $error("Adder sum mismatch");

  assert property (or_output == (selected_input | in_2))
    else $error("OR output mismatch");

  assert property (sum_output == sum[7:0])
    else $error("sum_output truncation mismatch");

  // Known-propagation (when inputs known, outputs must be known)
  assert property (!($isunknown({in_1, in_2, select})) |-> !($isunknown({selected_input, sum, sum_output, or_output})))
    else $error("Unknown X/Z propagated to outputs");

  // Stability: if inputs stable across cycles, outputs stable
  assert property ($stable({in_1, in_2, select}) |-> $stable({selected_input, sum, sum_output, or_output}))
    else $error("Outputs changed while inputs were stable");

  // Simple safety: MUX output must match one of the inputs
  assert property (selected_input inside {in_1, in_2})
    else $error("MUX output is neither in_1 nor in_2");

  // Coverage
  cover property (select == 1'b0);
  cover property (select == 1'b1);
  cover property (select ##1 !select);
  cover property (!select ##1 select);

  cover property (!($isunknown({selected_input, in_2})) && (sum[8] == 1'b1)); // carry out
  cover property (!($isunknown({selected_input, in_2})) && (sum[8] == 1'b0)); // no carry
endmodule

bind top_module top_module_sva u_top_module_sva (
  .clk           (clk),
  .reset         (reset),
  .in_1          (in_1),
  .in_2          (in_2),
  .select        (select),
  .sum_output    (sum_output),
  .or_output     (or_output),
  .selected_input(selected_input),
  .sum           (sum)
);