// SVA for axi_dwidth_converter_v2_1_b_downsizer
// Concise, high-value checks and coverage

module axi_dwidth_converter_v2_1_b_downsizer_sva #(
  parameter int C_AXI_ID_WIDTH = 1
)(
  input  logic                        ACLK,
  input  logic                        ARESET,

  input  logic                        cmd_valid,
  input  logic                        cmd_split,
  input  logic [7:0]                  cmd_repeat,
  input  logic                        cmd_ready,
  input  logic [C_AXI_ID_WIDTH-1:0]   cmd_id,

  input  logic [C_AXI_ID_WIDTH-1:0]   S_AXI_BID,
  input  logic [1:0]                  S_AXI_BRESP,
  input  logic                        S_AXI_BVALID,
  input  logic                        S_AXI_BREADY,

  input  logic [1:0]                  M_AXI_BRESP,
  input  logic                        M_AXI_BVALID,
  input  logic                        M_AXI_BREADY,

  // internal DUT signals
  input  logic                        last_word,
  input  logic                        first_mi_word,
  input  logic [7:0]                  repeat_cnt,
  input  logic [7:0]                  repeat_cnt_pre,
  input  logic [7:0]                  next_repeat_cnt,
  input  logic [1:0]                  S_AXI_BRESP_ACC,
  input  logic [1:0]                  S_AXI_BRESP_I,
  input  logic                        need_to_update_bresp
);

  wire pop_mi_data = M_AXI_BVALID && M_AXI_BREADY;

  // Environment assumptions (AXI-like)
  assume property (@(posedge ACLK) disable iff (ARESET)
    M_AXI_BVALID && !M_AXI_BREADY |-> $stable(M_AXI_BVALID) && $stable(M_AXI_BRESP));

  // Reset state
  assert property (@(posedge ACLK)
    ARESET |-> (first_mi_word && (repeat_cnt==8'b0) && (S_AXI_BRESP_ACC==2'b00)));

  // Ready/valid relations
  assert property (@(posedge ACLK) disable iff (ARESET)
    M_AXI_BREADY == (!last_word || S_AXI_BREADY));
  assert property (@(posedge ACLK) disable iff (ARESET)
    S_AXI_BVALID == (M_AXI_BVALID && last_word));

  // Output stability under backpressure
  assert property (@(posedge ACLK) disable iff (ARESET)
    S_AXI_BVALID && !S_AXI_BREADY |-> $stable(S_AXI_BRESP) && $stable(S_AXI_BID));

  // Command handshake formation
  assert property (@(posedge ACLK) disable iff (ARESET)
    cmd_ready == (cmd_valid && pop_mi_data && last_word));

  // Split/last_word/first relations
  assert property (@(posedge ACLK) disable iff (ARESET)
    last_word == (((repeat_cnt==8'd0) && !first_mi_word) || !cmd_split));
  assert property (@(posedge ACLK) disable iff (ARESET)
    cmd_split && first_mi_word |-> !last_word);
  assert property (@(posedge ACLK) disable iff (ARESET)
    !cmd_split |-> last_word);

  // Repeat count datapath
  assert property (@(posedge ACLK) disable iff (ARESET)
    first_mi_word |-> (repeat_cnt_pre == cmd_repeat));
  assert property (@(posedge ACLK) disable iff (ARESET)
    !first_mi_word |-> (repeat_cnt_pre == repeat_cnt));
  assert property (@(posedge ACLK) disable iff (ARESET)
    next_repeat_cnt == (repeat_cnt_pre - 8'd1));
  assert property (@(posedge ACLK) disable iff (ARESET)
    pop_mi_data |=> repeat_cnt == $past(next_repeat_cnt));
  assert property (@(posedge ACLK) disable iff (ARESET)
    pop_mi_data |=> first_mi_word == $past(last_word));

  // BRESP accumulation
  // Non-split: ACC mirrors current MI BRESP on each pop
  assert property (@(posedge ACLK) disable iff (ARESET)
    pop_mi_data && !cmd_split |=> S_AXI_BRESP_ACC == $past(M_AXI_BRESP));
  // Split first beat: ACC loads MI BRESP
  assert property (@(posedge ACLK) disable iff (ARESET)
    pop_mi_data && cmd_split && first_mi_word |=> S_AXI_BRESP_ACC == $past(M_AXI_BRESP));
  // Split next beats: ACC is max(prev ACC, MI BRESP)
  assert property (@(posedge ACLK) disable iff (ARESET)
    pop_mi_data && cmd_split && !first_mi_word |=> 
      (S_AXI_BRESP_ACC == $past(S_AXI_BRESP_ACC) || S_AXI_BRESP_ACC == $past(M_AXI_BRESP)));
  assert property (@(posedge ACLK) disable iff (ARESET)
    pop_mi_data && cmd_split && !first_mi_word |=> 
      (S_AXI_BRESP_ACC >= $past(S_AXI_BRESP_ACC) && S_AXI_BRESP_ACC >= $past(M_AXI_BRESP)));

  // BRESP on S-channel handshake
  assert property (@(posedge ACLK) disable iff (ARESET)
    S_AXI_BVALID && S_AXI_BREADY && !cmd_split |-> (S_AXI_BRESP == M_AXI_BRESP));
  assert property (@(posedge ACLK) disable iff (ARESET)
    S_AXI_BVALID && S_AXI_BREADY && cmd_split |-> 
      (S_AXI_BRESP == (need_to_update_bresp ? M_AXI_BRESP : S_AXI_BRESP_ACC)));

  // Coverage
  cover property (@(posedge ACLK) disable iff (ARESET)
    !cmd_split ##1 (S_AXI_BVALID && S_AXI_BREADY));
  cover property (@(posedge ACLK) disable iff (ARESET)
    cmd_split && first_mi_word && pop_mi_data ##[1:$]
    (pop_mi_data && need_to_update_bresp) ##[1:$]
    (S_AXI_BVALID && S_AXI_BREADY));
  cover property (@(posedge ACLK) disable iff (ARESET)
    last_word && M_AXI_BVALID && !S_AXI_BREADY [*2] ##1 (S_AXI_BREADY && S_AXI_BVALID));
  cover property (@(posedge ACLK) disable iff (ARESET)
    cmd_valid && !cmd_ready ##[1:10] (cmd_valid && cmd_ready));
  cover property (@(posedge ACLK) disable iff (ARESET)
    S_AXI_BVALID && S_AXI_BREADY && (S_AXI_BRESP!=2'b00));

endmodule

// Bind example (connects ports and selected internals)
bind axi_dwidth_converter_v2_1_b_downsizer
  axi_dwidth_converter_v2_1_b_downsizer_sva #(.C_AXI_ID_WIDTH(C_AXI_ID_WIDTH)) u_sva (
    .ACLK(ACLK),
    .ARESET(ARESET),
    .cmd_valid(cmd_valid),
    .cmd_split(cmd_split),
    .cmd_repeat(cmd_repeat),
    .cmd_ready(cmd_ready),
    .cmd_id(cmd_id),
    .S_AXI_BID(S_AXI_BID),
    .S_AXI_BRESP(S_AXI_BRESP),
    .S_AXI_BVALID(S_AXI_BVALID),
    .S_AXI_BREADY(S_AXI_BREADY),
    .M_AXI_BRESP(M_AXI_BRESP),
    .M_AXI_BVALID(M_AXI_BVALID),
    .M_AXI_BREADY(M_AXI_BREADY),
    .last_word(last_word),
    .first_mi_word(first_mi_word),
    .repeat_cnt(repeat_cnt),
    .repeat_cnt_pre(repeat_cnt_pre),
    .next_repeat_cnt(next_repeat_cnt),
    .S_AXI_BRESP_ACC(S_AXI_BRESP_ACC),
    .S_AXI_BRESP_I(S_AXI_BRESP_I),
    .need_to_update_bresp(need_to_update_bresp)
  );