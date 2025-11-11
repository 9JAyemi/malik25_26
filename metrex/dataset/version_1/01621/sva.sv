// SVA for core_if_id
// Bind this file to the DUT. Focuses on reset/flush semantics, write/update,
// stall/hold, and priority/coverage.

module core_if_id_sva (
  input logic        clk,
  input logic        rst,
  input logic        if_id_we,
  input logic        if_flush,
  input logic [31:0] pc_plus_4,
  input logic [31:0] inst_word,
  input logic [31:0] pc,
  input logic [31:0] pred_target,
  input logic [1:0]  delayed_PHT,
  input logic [2:0]  delayed_BHR,
  input logic [1:0]  btb_type,
  input logic        btb_v,
  input logic [31:0] pc_plus_4_out,
  input logic [31:0] inst_word_out,
  input logic [31:0] pc_out,
  input logic [31:0] pred_target_out,
  input logic [1:0]  delayed_PHT_out,
  input logic [2:0]  delayed_BHR_out,
  input logic [1:0]  btb_type_out,
  input logic        btb_v_out
);

  `define OUTS  {pc_plus_4_out, inst_word_out, pc_out, pred_target_out, delayed_PHT_out, delayed_BHR_out, btb_type_out, btb_v_out}
  `define INS   {pc_plus_4,     inst_word,     pc,     pred_target,     delayed_PHT,     delayed_BHR,     btb_type,     btb_v}
  `define ZEROS {32'h0000,32'h0000,32'h0000,32'h0000,2'b00,3'b000,2'b00,1'b0}

  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Reset or flush must clear all outputs to defined zeros on the next cycle.
  assert property (@(posedge clk)
                   (rst || if_flush) |=> (`OUTS == `ZEROS))
    else $error("core_if_id: reset/flush did not clear outputs");

  // Write enables update all outputs to the sampled inputs (no reset/flush).
  assert property (@(posedge clk) disable iff (rst)
                   (past_valid && if_id_we && !if_flush)
                   |=> (`OUTS == $past(`INS)))
    else $error("core_if_id: write-enable did not update outputs from inputs");

  // When stalled (no write, no reset/flush), outputs must hold their previous values.
  assert property (@(posedge clk) disable iff (rst || if_flush)
                   (past_valid && !if_id_we)
                   |=> (`OUTS == $past(`OUTS)))
    else $error("core_if_id: outputs changed during stall");

  // Flush has priority over write-enable when both asserted.
  assert property (@(posedge clk)
                   (if_flush && if_id_we) |=> (`OUTS == `ZEROS))
    else $error("core_if_id: flush did not take priority over write");

  // Coverage: exercise key behaviors
  cover property (@(posedge clk) rst);
  cover property (@(posedge clk) if_flush);
  cover property (@(posedge clk) !rst && !if_flush && if_id_we);
  cover property (@(posedge clk) !rst && !if_flush && !if_id_we);
  cover property (@(posedge clk) (if_flush && if_id_we));              // priority case
  cover property (@(posedge clk) (!rst && !if_flush && if_id_we)[*2]); // back-to-back writes
  cover property (@(posedge clk) (!rst && !if_flush && if_id_we ##1 !if_flush && !if_id_we)); // write then stall

endmodule

bind core_if_id core_if_id_sva core_if_id_sva_b (
  .clk(clk),
  .rst(rst),
  .if_id_we(if_id_we),
  .if_flush(if_flush),
  .pc_plus_4(pc_plus_4),
  .inst_word(inst_word),
  .pc(pc),
  .pred_target(pred_target),
  .delayed_PHT(delayed_PHT),
  .delayed_BHR(delayed_BHR),
  .btb_type(btb_type),
  .btb_v(btb_v),
  .pc_plus_4_out(pc_plus_4_out),
  .inst_word_out(inst_word_out),
  .pc_out(pc_out),
  .pred_target_out(pred_target_out),
  .delayed_PHT_out(delayed_PHT_out),
  .delayed_BHR_out(delayed_BHR_out),
  .btb_type_out(btb_type_out),
  .btb_v_out(btb_v_out)
);