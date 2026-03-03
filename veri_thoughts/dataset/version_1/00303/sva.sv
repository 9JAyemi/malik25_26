// SVA for xor_adder
module xor_adder_sva (
  input clk,
  input [1:0] a,
  input [1:0] b,
  input [1:0] sum
);
  bit init;
  initial init = 0;
  always @(posedge clk) init <= 1;

  default clocking cb @(posedge clk); endclocking

  // Sanity: inputs known each cycle
  ap_inputs_known: assert property (!$isunknown({a,b}));

  // Functional correctness: 1-cycle latency XOR (only when past inputs were known)
  ap_func: assert property (init && !$isunknown($past({a,b})) |-> sum == ($past(a) ^ $past(b)));

  // Output should be known when driven from known past inputs
  ap_sum_known: assert property (init && !$isunknown($past({a,b})) |-> !$isunknown(sum));

  // No glitches between clock edges
  ap_no_glitch_negedge: assert property (@(negedge clk) $stable(sum));

  // Coverage: all input combinations hit
  genvar gi;
  generate
    for (gi = 0; gi < 16; gi++) begin : C_IN_ALL
      cover property (@(posedge clk) {a,b} == gi);
    end
  endgenerate

  // Coverage: each sum value seen; each sum bit toggles
  genvar gs;
  generate
    for (gs = 0; gs < 4; gs++) begin : C_SUM_ALL
      cover property (@(posedge clk) sum == gs);
    end
  endgenerate
  c_sum0_tgl: cover property (@(posedge clk) $changed(sum[0]));
  c_sum1_tgl: cover property (@(posedge clk) $changed(sum[1]));
endmodule

// Bind into DUT
bind xor_adder xor_adder_sva sva_inst (.clk(clk), .a(a), .b(b), .sum(sum));