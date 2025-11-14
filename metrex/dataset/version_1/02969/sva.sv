// SVA for parity_generator: concise, high-quality checks and coverage
// Bind example (in your TB): bind parity_generator parity_generator_sva #(.WIDTH(8)) u_sva (.*);

module parity_generator_sva #(parameter int WIDTH = 8)
(
  input  logic                 clk,
  input  logic [WIDTH-1:0]     in,
  input  logic                 parity_bit,

  // Optional internal taps (connect via bind if available)
  input  logic [WIDTH-1:0]     in_reg,
  input  logic                 parity_calculated
);

  default clocking cb @(posedge clk); endclocking

  // Track pipeline warm-up
  logic past1;
  always_ff @(posedge clk) past1 <= 1'b1;

  // Core functional check: 2-cycle latency from input to parity_bit
  // Gate on known inputs to avoid X-propagation issues (no reset in DUT)
  property p_parity_2cycle;
    past1 && $past(past1) && !$isunknown($past(in,2)) |->
      parity_bit === ^$past(in,2);
  endproperty
  a_parity_2cycle: assert property (p_parity_2cycle);

  // Output should be known once pipeline is filled
  a_no_x_out: assert property (past1 && $past(past1) |-> !$isunknown(parity_bit));

  // Optional micro-architecture checks (enabled only if internals are connected and known)
  a_in_reg_pipeline: assert property (past1 && !$isunknown($past(in)) && !$isunknown(in_reg) |-> in_reg === $past(in));

  a_parity_stage_link: assert property (past1 && !$isunknown($past(parity_calculated)) |-> parity_bit === $past(parity_calculated));

  // Intended parity calculation stage (will flag the loop/NBA bug if present)
  a_calc_matches_xor: assert property (past1 && !$isunknown($past(in_reg)) |-> $past(parity_calculated) === ^$past(in_reg));

  // Functional coverage
  // See both parity outcomes (after pipeline warm-up)
  c_seen_parity0: cover property (past1 && $past(past1) && !$isunknown($past(in,2)) && (^$past(in,2) == 1'b0) && (parity_bit == 1'b0));
  c_seen_parity1: cover property (past1 && $past(past1) && !$isunknown($past(in,2)) && (^$past(in,2) == 1'b1) && (parity_bit == 1'b1));

  // Parity_bit toggles observed
  c_parity_toggle: cover property (past1 && $past(past1) && $changed(parity_bit));

  // Each single-bit toggle (between t-3 and t-2) flips parity_bit (between t-1 and t)
  c_bit_influence: cover property (past1 && $past(past1) && $past(past1,1) &&
                                   $onehot($past(in,3) ^ $past(in,2)) &&
                                   (parity_bit != $past(parity_bit)));

  // Some useful 8-bit corner cases (active when WIDTH==8)
  generate if (WIDTH == 8) begin
    c_all_zero: cover property (past1 && $past(past1) && ($past(in,2) == 8'h00) && (parity_bit == 1'b0));
    c_all_one : cover property (past1 && $past(past1) && ($past(in,2) == 8'hFF) && (parity_bit == 1'b0));
    c_aa_55   : cover property (past1 && $past(past1) && ($past(in,2) inside {8'hAA, 8'h55}));
  end endgenerate

endmodule