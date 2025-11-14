// SVA for axi_dwidth_converter_v2_1_7_b_downsizer
// Bind as: bind axi_dwidth_converter_v2_1_7_b_downsizer axi_dwidth_converter_v2_1_7_b_downsizer_sva #(.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH)) sva_i (.*);

module axi_dwidth_converter_v2_1_7_b_downsizer_sva
  #(parameter int C_AXI_ID_WIDTH = 1)
(
  // DUT ports
  input  logic                       ARESET,
  input  logic                       ACLK,
  input  logic                       cmd_valid,
  input  logic                       cmd_split,
  input  logic [7:0]                 cmd_repeat,
  input  logic                       cmd_ready,
  input  logic [C_AXI_ID_WIDTH-1:0]  cmd_id,

  input  logic [1:0]                 M_AXI_BRESP,
  input  logic                       M_AXI_BVALID,
  input  logic                       M_AXI_BREADY,

  input  logic [C_AXI_ID_WIDTH-1:0]  S_AXI_BID,
  input  logic [1:0]                 S_AXI_BRESP,
  input  logic                       S_AXI_BVALID,
  input  logic                       S_AXI_BREADY,

  // DUT internals used by SVA
  input  logic                       mi_stalling,
  input  logic                       pop_mi_data,
  input  logic                       first_mi_word,
  input  logic                       last_word,
  input  logic [7:0]                 repeat_cnt_pre,
  input  logic [7:0]                 repeat_cnt,
  input  logic [7:0]                 next_repeat_cnt,
  input  logic [1:0]                 S_AXI_BRESP_ACC,
  input  logic [1:0]                 S_AXI_BRESP_I,
  input  logic                       S_AXI_BVALID_I,
  input  logic                       S_AXI_BREADY_I,
  input  logic                       M_AXI_BREADY_I,
  input  logic                       need_to_update_bresp
);

  // ----------------------------------------
  // Handshake/basic equivalences
  // ----------------------------------------
  // Ready relation: M_READY = S_READY | ~last_word
  assert property (@(posedge ACLK) disable iff (ARESET)
    M_AXI_BREADY == (S_AXI_BREADY | ~last_word)
  );

  // pop_mi_data correctness
  assert property (@(posedge ACLK) disable iff (ARESET)
    pop_mi_data == (M_AXI_BVALID & M_AXI_BREADY)
  );

  // S BVALID generated only on last_word and equals M BVALID & last_word
  assert property (@(posedge ACLK) disable iff (ARESET)
    S_AXI_BVALID == (M_AXI_BVALID & last_word)
  );

  // S BVALID must be held high until accepted (AXI rule)
  assert property (@(posedge ACLK) disable iff (ARESET)
    S_AXI_BVALID && !S_AXI_BREADY |=> S_AXI_BVALID
  );

  // S BID must follow cmd_id and be stable while stalled
  assert property (@(posedge ACLK) disable iff (ARESET)
    S_AXI_BID == cmd_id
  );
  assert property (@(posedge ACLK) disable iff (ARESET)
    S_AXI_BVALID && !S_AXI_BREADY |-> $stable(S_AXI_BID)
  );

  // S BRESP stable while stalled
  assert property (@(posedge ACLK) disable iff (ARESET)
    S_AXI_BVALID && !S_AXI_BREADY |-> $stable(S_AXI_BRESP)
  );

  // cmd_ready correctness
  assert property (@(posedge ACLK) disable iff (ARESET)
    cmd_ready == (cmd_valid & pop_mi_data & last_word)
  );

  // ----------------------------------------
  // BRESP aggregation/selection
  // ----------------------------------------
  // Non-split: direct pass-through of BRESP
  assert property (@(posedge ACLK) disable iff (ARESET)
    !cmd_split |-> (S_AXI_BRESP == M_AXI_BRESP)
  );

  // Split: on first beat load from M, otherwise max-accumulate
  assert property (@(posedge ACLK) disable iff (ARESET)
    cmd_split && first_mi_word |-> (S_AXI_BRESP == M_AXI_BRESP)
  );

  assert property (@(posedge ACLK) disable iff (ARESET)
    cmd_split && !first_mi_word && (M_AXI_BRESP > S_AXI_BRESP_ACC) |-> (S_AXI_BRESP == M_AXI_BRESP)
  );

  assert property (@(posedge ACLK) disable iff (ARESET)
    cmd_split && !first_mi_word && !(M_AXI_BRESP > S_AXI_BRESP_ACC) |-> (S_AXI_BRESP == S_AXI_BRESP_ACC)
  );

  // BRESP_ACC reset and update behavior
  assert property (@(posedge ACLK) ARESET |-> (S_AXI_BRESP_ACC == 2'b00));
  assert property (@(posedge ACLK) disable iff (ARESET)
    pop_mi_data |=> (S_AXI_BRESP_ACC == $past(S_AXI_BRESP_I))
  );

  // Monotonic non-decreasing accumulator during a split transfer
  assert property (@(posedge ACLK) disable iff (ARESET)
    pop_mi_data && cmd_split |=> (S_AXI_BRESP_ACC >= $past(S_AXI_BRESP_ACC))
  );

  // ----------------------------------------
  // Counter/last_word logic
  // ----------------------------------------
  assert property (@(posedge ACLK) disable iff (ARESET)
    last_word == ( ((repeat_cnt == 8'h00) && !first_mi_word) || !cmd_split )
  );

  assert property (@(posedge ACLK) disable iff (ARESET)
    repeat_cnt_pre == (first_mi_word ? cmd_repeat : repeat_cnt)
  );

  assert property (@(posedge ACLK) disable iff (ARESET)
    next_repeat_cnt == (repeat_cnt_pre - 8'h01)
  );

  assert property (@(posedge ACLK) ARESET |-> (repeat_cnt == 8'h00) && first_mi_word);

  assert property (@(posedge ACLK) disable iff (ARESET)
    pop_mi_data |=> (repeat_cnt == $past(next_repeat_cnt)) && (first_mi_word == $past(last_word))
  );

  // Internal aliases
  assert property (@(posedge ACLK) disable iff (ARESET) M_AXI_BREADY_I == M_AXI_BREADY);
  assert property (@(posedge ACLK) disable iff (ARESET) S_AXI_BREADY_I == S_AXI_BREADY);
  assert property (@(posedge ACLK) disable iff (ARESET) S_AXI_BVALID_I == S_AXI_BVALID);
  assert property (@(posedge ACLK) disable iff (ARESET) S_AXI_BRESP   == S_AXI_BRESP_I);

  // ----------------------------------------
  // Coverage
  // ----------------------------------------
  // 1) Split transaction with escalation (need_to_update_bresp), then final handshake
  cover property (@(posedge ACLK) disable iff (ARESET)
    cmd_split && first_mi_word ##1
    pop_mi_data ##[1:$]
    (cmd_split && pop_mi_data && need_to_update_bresp) ##[1:$]
    (S_AXI_BVALID && S_AXI_BREADY)
  );

  // 2) Non-split pass-through with immediate handshake
  cover property (@(posedge ACLK) disable iff (ARESET)
    !cmd_split && M_AXI_BVALID && S_AXI_BREADY ##1 (S_AXI_BVALID && S_AXI_BREADY)
  );

  // 3) Backpressure on S side then accept
  cover property (@(posedge ACLK) disable iff (ARESET)
    S_AXI_BVALID && !S_AXI_BREADY ##[1:$] (S_AXI_BVALID && S_AXI_BREADY)
  );

  // 4) Multi-beat split counting down to last_word
  cover property (@(posedge ACLK) disable iff (ARESET)
    cmd_split && first_mi_word ##1
    pop_mi_data [*2] ##[1:$]
    last_word ##1 (S_AXI_BVALID && S_AXI_BREADY)
  );

endmodule

bind axi_dwidth_converter_v2_1_7_b_downsizer
  axi_dwidth_converter_v2_1_7_b_downsizer_sva #(.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH)) sva_i (.*);