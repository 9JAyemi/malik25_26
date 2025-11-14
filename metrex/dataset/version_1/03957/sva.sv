// SVA for register_addition
// Focus: 1-cycle latency from inputs/mode to outputs; correct sum and flags; reset; coverage.

`ifndef REGISTER_ADDITION_SVA
`define REGISTER_ADDITION_SVA

bind register_addition register_addition_sva u_register_addition_sva
(
  .clk(clk),
  .reset(reset),
  .mode(mode),
  .a(a),
  .b(b),
  .sum(sum),
  .flags(flags)
);

module register_addition_sva
(
  input logic        clk,
  input logic        reset,
  input logic [1:0]  mode,
  input logic [29:0] a,
  input logic [29:0] b,
  input logic [29:0] sum,
  input logic [3:0]  flags
);
  localparam int W = 30;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Helpers (all $past refer to the producing cycle 1 clk earlier)
  let A_p  = $past(a);
  let B_p  = $past(b);
  let M_p  = $past(mode);
  let u_sum_ext = {1'b0, A_p} + {1'b0, B_p}; // [W:0]
  let s_sum_ext = $signed({A_p[W-1],A_p}) + $signed({B_p[W-1],B_p}); // signed [W:0]
  let exp_sum   = u_sum_ext[W-1:0];          // modulo-W sum (same for signed/unsigned)
  let u_ovf     = u_sum_ext[W];              // carry-out
  let s_ovf     = s_sum_ext[W] != s_sum_ext[W-1]; // signed overflow

  // Reset behavior
  assert property (reset |-> (sum == '0 && flags == 4'b0000));

  // Sum value and 1-cycle latency
  assert property (!reset && $past(!reset) |-> sum == exp_sum);

  // Flags correctness: unsigned mode (mode==0 in producing cycle)
  assert property (!reset && $past(!reset) && (M_p == 2'b00) |->
                   (u_ovf ? (flags == 4'b0001) : (flags == 4'b0000)));

  // Flags correctness: signed mode (any nonzero mode treated as signed)
  assert property (!reset && $past(!reset) && (M_p != 2'b00) |->
                   (s_ovf ? (flags == 4'b0010) : (flags == 4'b0000)));

  // Flags use only defined encodings
  assert property (!reset && $past(!reset) |->
                   (flags inside {4'b0000,4'b0001,4'b0010}));

  // No X on outputs once out of reset
  assert property (!reset && $past(!reset) |->
                   !$isunknown({sum,flags}));

  // Coverage: unsigned no-ovf and ovf
  cover property (!reset && $past(!reset) && (M_p==2'b00) && !u_ovf && (flags==4'b0000));
  cover property (!reset && $past(!reset) && (M_p==2'b00) &&  u_ovf && (flags==4'b0001));

  // Coverage: signed no-ovf, positive ovf, negative ovf
  cover property (!reset && $past(!reset) && (M_p!=2'b00) && !s_ovf && (flags==4'b0000));
  cover property (!reset && $past(!reset) && (M_p!=2'b00) &&  s_ovf && (flags==4'b0010) && (s_sum_ext[W-1]==1'b0));
  cover property (!reset && $past(!reset) && (M_p!=2'b00) &&  s_ovf && (flags==4'b0010) && (s_sum_ext[W-1]==1'b1));

  // Coverage: mode transitions
  cover property (!reset && $past(!reset) && (M_p==2'b00) ##1 (mode!=2'b00));
  cover property (!reset && $past(!reset) && (M_p!=2'b00) ##1 (mode==2'b00));

endmodule

`endif