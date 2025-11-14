// SVA for top_module and internal adders
module top_module_sva (
  input logic         clk,
  input logic         reset,
  input logic [31:0]  a,
  input logic [31:0]  b,
  input logic [31:0]  adder1_out,
  input logic [31:0]  adder2_out,
  input logic [31:0]  sum
);
  default clocking cb @(posedge clk); endclocking

  // Basic X/Z checks
  ap_no_x_inputs:  assert property (disable iff (reset) !$isunknown({a,b}));
  ap_no_x_outputs: assert property (disable iff (reset) !$isunknown({adder1_out,adder2_out,sum}));

  // Reset behavior
  ap_reset_sum_zero: assert property (reset |-> (sum == 32'h0));

  // Each adder must compute a+b (mod 2^32)
  ap_adder1_adds: assert property (disable iff (reset) adder1_out == (a + b));
  ap_adder2_adds: assert property (disable iff (reset) adder2_out == (a + b));

  // Top-level function: registered a+b
  ap_sum_next_eq_add: assert property (disable iff (reset) 1 |=> (reset or (sum == (a + b))));

  // Selection correctness: next cycle equals current cycle's max(adder1_out, adder2_out)
  ap_select_is_max: assert property (disable iff (reset)
                                     1 |=> (reset or (sum == ((adder1_out > adder2_out) ? adder1_out : adder2_out))));

  // Optional: sum comes from one of the adders (previous cycle)
  ap_sum_from_either: assert property (disable iff (reset)
                                       1 |=> (reset or (sum == adder1_out) or (sum == adder2_out)));

  // Coverage
  cp_reset:                cover property ($rose(reset));
  cp_branch_adder1_higher: cover property (disable iff (reset) (adder1_out > adder2_out));
  cp_branch_adder2_ge:     cover property (disable iff (reset) (adder2_out >= adder1_out));
  cp_overflow:             cover property (disable iff (reset) ((a + b) < a)); // unsigned wrap
  cp_extremes:             cover property (disable iff (reset) ((a==32'h0 && b==32'h0) or
                                                                (a==32'hFFFF_FFFF && b==32'h1)));
endmodule

// Bind into DUT (accessing internal nets adder1_out/adder2_out)
bind top_module top_module_sva top_module_sva_i (
  .clk         (clk),
  .reset       (reset),
  .a           (a),
  .b           (b),
  .adder1_out  (adder1_out),
  .adder2_out  (adder2_out),
  .sum         (sum)
);