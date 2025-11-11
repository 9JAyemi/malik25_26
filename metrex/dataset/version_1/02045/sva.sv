// SVA for count_ones
// Bind this checker to the DUT: bind count_ones count_ones_sva sv(.clk(clk), .in(in), .out(out), .in_reg(in_reg), .in_reg_pipe1(in_reg_pipe1), .in_reg_pipe32(in_reg_pipe32), .sum_reg(sum_reg), .sum_reg_pipe31(sum_reg_pipe31), .sum_reg_pipe32(sum_reg_pipe32));

module count_ones_sva (
  input logic        clk,
  input logic [31:0] in,
  input logic [5:0]  out,
  input logic [31:0] in_reg,
  input logic [31:0] in_reg_pipe1,
  input logic [31:0] in_reg_pipe32,
  input logic [31:0] sum_reg,
  input logic [31:0] sum_reg_pipe31,
  input logic [31:0] sum_reg_pipe32
);

  // simple pipeline warmup (no reset in DUT)
  logic [2:0] warm_cnt;
  logic       initdone;
  always_ff @(posedge clk) begin
    if (!initdone) warm_cnt <= warm_cnt + 3'd1;
    initdone <= (warm_cnt == 3'd6);
  end

  default clocking cb @(posedge clk); endclocking
  default disable iff (!initdone);

  // In pipeline timing
  a_in_reg:       assert property (in_reg       == $past(in));
  a_in_pipe1:     assert property (in_reg_pipe1 == $past(in_reg));
  a_in_pipe32:    assert property (in_reg_pipe32== $past(in_reg_pipe1));

  // Sum pipeline timing
  a_sum_pipe31:   assert property (sum_reg_pipe31 == $past(sum_reg));
  a_sum_pipe32:   assert property (sum_reg_pipe32 == $past(sum_reg_pipe31));

  // Sum update equation (local register view)
  a_sum_eq_local: assert property (sum_reg == $past(sum_reg_pipe31) + $past(in_reg_pipe32));

  // Sum update equation (bridged to primary input)
  a_sum_eq_in:    assert property (sum_reg == $past(sum_reg,2) + $past(in,4));

  // Output mapping and latency
  a_out_map:      assert property (out == sum_reg_pipe32[5:0]);
  a_out_delay:    assert property (out == $past(sum_reg,2)[5:0]);

  // Cross-check: sum_reg_pipe32 mirrors sum_reg two cycles earlier
  a_sum_pipe32_equiv: assert property (sum_reg_pipe32 == $past(sum_reg,2));

  // Basic X/Z safety on observable output
  a_out_known:    assert property (!$isunknown(out));

  // Coverage: exercise full data path from input to output
  // Non-zero input value flows through in-pipe, contributes to sum, then appears on out after total latency
  c_in_to_out: cover property (
      (in != 32'h0)
    ##3 (in_reg_pipe32 == $past(in,3))
    ##1 (sum_reg == $past(sum_reg_pipe31) + $past(in_reg_pipe32))
    ##2 (out == $past(sum_reg,2)[5:0])
  );

  // Coverage: observe sum feedback + add interaction at least once
  c_sum_feedback: cover property ($changed(sum_reg) ##2 (sum_reg_pipe32 == $past(sum_reg,2)));

endmodule