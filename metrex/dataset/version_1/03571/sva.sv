// SVA for byte_reverse_pipeline
module byte_reverse_pipeline_sva
(
  input  logic        clk,
  input  logic        reset,
  input  logic [31:0] in,
  input  logic [31:0] out,
  input  logic [7:0]  shift_reg [3:0],
  input  logic [1:0]  stage
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  function automatic logic [31:0] rev_bytes32 (input logic [31:0] v);
    return {v[7:0],v[15:8],v[23:16],v[31:24]};
  endfunction

  // Basic hygiene
  a_stage_known:    assert property (!$isunknown(stage) && stage inside {2'd0,2'd1,2'd2});
  a_regs_known:     assert property (!$isunknown({shift_reg[0],shift_reg[1],shift_reg[2],shift_reg[3]}));
  a_out_known:      assert property (!$isunknown(out));

  // Reset behavior
  a_reset_zero:     assert property (@(posedge clk) reset |-> stage==2'd0 &&
                                     shift_reg[0]==8'h0 && shift_reg[1]==8'h0 &&
                                     shift_reg[2]==8'h0 && shift_reg[3]==8'h0 &&
                                     out==32'h0);

  // Stage sequencing
  a_0_to_1:         assert property (stage==2'd0 |=> stage==2'd1);
  a_1_to_2:         assert property (stage==2'd1 |=> stage==2'd2);
  a_2_to_0:         assert property (stage==2'd2 |=> stage==2'd0);

  // Per-stage data transforms (as coded)
  a_cap_on_0:       assert property (stage==2'd0 |=> shift_reg[0]==$past(in[7:0])   &&
                                                shift_reg[1]==$past(in[15:8])  &&
                                                shift_reg[2]==$past(in[23:16]) &&
                                                shift_reg[3]==$past(in[31:24]));
  a_swap_on_1:      assert property (stage==2'd1 |=> shift_reg[0]==$past(shift_reg[2]) &&
                                                shift_reg[1]==$past(shift_reg[3]) &&
                                                shift_reg[2]==$past(shift_reg[0]) &&
                                                shift_reg[3]==$past(shift_reg[1]));
  a_clear_on_2:     assert property (stage==2'd2 |=> shift_reg[0]==8'h0 && shift_reg[1]==8'h0 &&
                                                shift_reg[2]==8'h0 && shift_reg[3]==8'h0 &&
                                                out==32'h0);

  // Output wiring
  a_out_concat:     assert property (out == {shift_reg[3],shift_reg[2],shift_reg[1],shift_reg[0]});

  // Spec-level check: output is byte-reversed one cycle after capture (should hold at stage==1)
  a_func_byte_rev:  assert property (stage==2'd1 && $past(stage)==2'd0 |->
                                     out == rev_bytes32($past(in)));

  // Coverage
  c_stage_cycle:    cover property (stage==2'd0 ##1 stage==2'd1 ##1 stage==2'd2 ##1 stage==2'd0);
  c_nonzero_rev:    cover property (stage==2'd0 && in!=32'h0 ##1 stage==2'd1 && out==rev_bytes32($past(in)));
  c_clear:          cover property (stage==2'd2 ##1 out==32'h0);

endmodule

bind byte_reverse_pipeline byte_reverse_pipeline_sva
(
  .clk(clk),
  .reset(reset),
  .in(in),
  .out(out),
  .shift_reg(shift_reg),
  .stage(stage)
);