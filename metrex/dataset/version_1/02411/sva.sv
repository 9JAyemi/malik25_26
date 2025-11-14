// SVA for pipelined_4bit_adder
// Bind this file to the DUT: bind pipelined_4bit_adder pipelined_4bit_adder_sva sva();

module pipelined_4bit_adder_sva
(
  input  logic                 clk,
  input  logic signed   [3:0]  A,
  input  logic signed   [3:0]  B,
  input  logic signed   [3:0]  sum,
  input  logic                 carry_out,

  // internal DUT regs (connected via bind)
  input  logic signed   [3:0]  stage1_sum,
  input  logic                 stage1_carry_out,
  input  logic signed   [3:0]  stage2_sum,
  input  logic                 stage2_carry_out
);

  default clocking cb @(posedge clk); endclocking

  // Basic X checks
  a_no_x_comb: assert property (!$isunknown({A,B})) |-> !$isunknown({stage1_sum,stage1_carry_out}));
  a_no_x_pipe: assert property (!$isunknown({stage1_sum,stage1_carry_out})) |-> !$isunknown({stage2_sum,stage2_carry_out}));
  a_no_x_out:  assert property (!$isunknown({stage2_sum,stage2_carry_out})) |-> !$isunknown({sum,carry_out});

  // Combinational correctness of stage1 (sum + carry as a 5-bit add)
  a_comb_full: assert property ({stage1_carry_out, stage1_sum} == {1'b0, A} + {1'b0, B});

  // Pipeline register transfer correctness
  a_pipe_cap:  assert property ({stage2_carry_out, stage2_sum} == $past({stage1_carry_out, stage1_sum}));

  // Output mapping to stage2 regs
  a_out_map:   assert property ({carry_out, sum} == {stage2_carry_out, stage2_sum});

  // Outputs only change on clock edges (glitch-free)
  a_glitch_free: assert property (@(negedge clk) $stable({sum,carry_out}));

  // Optional end-to-end latency check when inputs are edge-stable
  a_end_to_end_latency: assert property (
    ($past({A,B}) == {A,B}) |-> {carry_out, sum} == {1'b0, $past(A)} + {1'b0, $past(B)}
  );

  // Functional coverage (key scenarios)
  c_carry0:     cover property (stage1_carry_out == 1'b0);
  c_carry1:     cover property (stage1_carry_out == 1'b1);
  c_zero_zero:  cover property (A == 4'sd0 && B == 4'sd0);
  c_max_max:    cover property (A == 4'sd7 && B == 4'sd7 && stage1_carry_out == 1'b0);
  c_min_min:    cover property (A == 4'sd-8 && B == 4'sd-8 && stage1_carry_out == 1'b1);
  c_pos_neg:    cover property (A[3]==1'b0 && B[3]==1'b1);
  c_neg_pos:    cover property (A[3]==1'b1 && B[3]==1'b0);
  c_back2back:  cover property ($changed({A,B}) ##1 $changed({A,B}));
  c_pipe_seen:  cover property ({carry_out, sum} == $past({stage1_carry_out, stage1_sum}));

endmodule