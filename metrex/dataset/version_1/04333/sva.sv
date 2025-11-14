// SVA for reg_8bit: concise, high-quality checks and coverage
module reg_8bit_sva #(parameter WIDTH=8) (
  input  logic                 clk,
  input  logic                 not_reset,   // async active-low
  input  logic                 Load,
  input  logic [WIDTH-1:0]     D,
  input  logic [WIDTH-1:0]     Q
);

  // past-valid guard for $past usage
  bit past_valid;
  always @(posedge clk or negedge not_reset)
    if (!not_reset) past_valid <= 1'b0;
    else            past_valid <= 1'b1;

  // Default clocking and reset-disable for concurrent SVA
  default clocking cb @(posedge clk); endclocking
  default disable iff (!not_reset);

  // Functional correctness
  assert property (past_valid && Load  |=> Q == $past(D));       // Load captures D
  assert property (past_valid && !Load |=> Q == $past(Q));       // Hold when not loading
  assert property (past_valid && (Q != $past(Q)) |-> $past(Load)); // Q changes only if Load

  // Asynchronous reset behavior
  assert property (@(posedge clk) !not_reset |-> Q == '0);       // Q forced 0 while in reset
  // Immediate assertion at async reset edge to catch intra-cycle behavior
  always @(negedge not_reset) assert (Q == '0);

  // X/Z sanity (when meaningful)
  assert property (!$isunknown(Q));
  assert property (Load |-> !$isunknown(D));

  // Coverage: reset, load patterns, and bit toggles
  cover property (@(posedge clk) $fell(not_reset));
  cover property (@(posedge clk) $rose(not_reset));
  cover property (Load && (D == '0));
  cover property (Load && (D == {WIDTH{1'b1}}));

  genvar i;
  generate
    for (i = 0; i < WIDTH; i++) begin : COV_BITS
      cover property ($rose(Q[i]));
      cover property ($fell(Q[i]));
    end
  endgenerate

endmodule

// Bind into DUT
bind reg_8bit reg_8bit_sva #(.WIDTH(8)) reg_8bit_sva_i (
  .clk       (clk),
  .not_reset (not_reset),
  .Load      (Load),
  .D         (D),
  .Q         (Q)
);