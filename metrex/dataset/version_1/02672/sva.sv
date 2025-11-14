// SVA for preprocess_control
// Bind module with concise but strong checks and coverage

module preprocess_control_sva
  #(parameter DATA_WIDTH = 64,
    parameter CTRL_WIDTH = DATA_WIDTH/8)
(
  input  logic                        clk,
  input  logic                        reset,

  input  logic [CTRL_WIDTH-1:0]       in_ctrl,
  input  logic                        in_wr,

  input  logic                        word_MAC_DA_HI,
  input  logic                        word_MAC_DASA,
  input  logic                        word_MAC_SA_LO,
  input  logic                        word_ETH_IP_VER,
  input  logic                        word_IP_LEN_ID,
  input  logic                        word_IP_FRAG_TTL_PROTO,
  input  logic                        word_IP_CHECKSUM_SRC_HI,
  input  logic                        word_IP_SRC_DST,
  input  logic                        word_IP_DST_LO,

  input  logic [6:0]                  state
);

  // Mirror DUT state encodings
  localparam SKIP_MODULE_HDRS      = 7'd1;
  localparam WORD_1                = 7'd2;
  localparam WORD_2                = 7'd4;
  localparam WORD_3                = 7'd8;
  localparam WORD_4                = 7'd16;
  localparam WAIT_EOP              = 7'd64;

  // Shorthand
  function automatic bit is_ctrl0;  return (in_ctrl == '0); endfunction
  function automatic bit is_ctrlnz; return (in_ctrl != '0); endfunction

  // 1) Reset and legal encoding
  assert property (@(posedge clk) reset |=> state == SKIP_MODULE_HDRS)
    else $error("State not SKIP on reset release");

  assert property (@(posedge clk) disable iff (reset)
                   state inside {SKIP_MODULE_HDRS, WORD_1, WORD_2, WORD_3, WORD_4, WAIT_EOP})
    else $error("Illegal state encoding");

  // 2) Outputs only when in_wr
  assert property (@(posedge clk) disable iff (reset)
                   !in_wr |-> !(word_MAC_DA_HI | word_MAC_DASA | word_MAC_SA_LO | word_ETH_IP_VER |
                                word_IP_LEN_ID | word_IP_FRAG_TTL_PROTO | word_IP_CHECKSUM_SRC_HI |
                                word_IP_SRC_DST | word_IP_DST_LO))
    else $error("Outputs asserted without in_wr");

  // 3) Per-state output pattern and next-state on enable
  // SKIP: need in_ctrl==0 & in_wr to start
  assert property (@(posedge clk) disable iff (reset)
    (state==SKIP_MODULE_HDRS && in_wr && is_ctrl0()) |->
      (word_MAC_DA_HI && word_MAC_DASA &&
       !(word_MAC_SA_LO | word_ETH_IP_VER | word_IP_LEN_ID | word_IP_FRAG_TTL_PROTO |
         word_IP_CHECKSUM_SRC_HI | word_IP_SRC_DST | word_IP_DST_LO)) ##1
      state==WORD_1)
    else $error("SKIP enable: bad outputs or next state");

  // Hold in SKIP otherwise
  assert property (@(posedge clk) disable iff (reset)
    (state==SKIP_MODULE_HDRS && !(in_wr && is_ctrl0())) |=> state==SKIP_MODULE_HDRS)
    else $error("SKIP hold violated");

  // WORD_1
  assert property (@(posedge clk) disable iff (reset)
    (state==WORD_1 && in_wr) |->
      (word_MAC_SA_LO && word_ETH_IP_VER &&
       !(word_MAC_DA_HI | word_MAC_DASA | word_IP_LEN_ID | word_IP_FRAG_TTL_PROTO |
         word_IP_CHECKSUM_SRC_HI | word_IP_SRC_DST | word_IP_DST_LO)) ##1
      state==WORD_2)
    else $error("WORD_1 enable: bad outputs or next state");

  assert property (@(posedge clk) disable iff (reset)
    (state==WORD_1 && !in_wr) |=> state==WORD_1)
    else $error("WORD_1 hold violated");

  // WORD_2
  assert property (@(posedge clk) disable iff (reset)
    (state==WORD_2 && in_wr) |->
      (word_IP_LEN_ID && word_IP_FRAG_TTL_PROTO &&
       !(word_MAC_DA_HI | word_MAC_DASA | word_MAC_SA_LO | word_ETH_IP_VER |
         word_IP_CHECKSUM_SRC_HI | word_IP_SRC_DST | word_IP_DST_LO)) ##1
      state==WORD_3)
    else $error("WORD_2 enable: bad outputs or next state");

  assert property (@(posedge clk) disable iff (reset)
    (state==WORD_2 && !in_wr) |=> state==WORD_2)
    else $error("WORD_2 hold violated");

  // WORD_3
  assert property (@(posedge clk) disable iff (reset)
    (state==WORD_3 && in_wr) |->
      (word_IP_CHECKSUM_SRC_HI && word_IP_SRC_DST &&
       !(word_MAC_DA_HI | word_MAC_DASA | word_MAC_SA_LO | word_ETH_IP_VER |
         word_IP_LEN_ID | word_IP_FRAG_TTL_PROTO | word_IP_DST_LO)) ##1
      state==WORD_4)
    else $error("WORD_3 enable: bad outputs or next state");

  assert property (@(posedge clk) disable iff (reset)
    (state==WORD_3 && !in_wr) |=> state==WORD_3)
    else $error("WORD_3 hold violated");

  // WORD_4
  assert property (@(posedge clk) disable iff (reset)
    (state==WORD_4 && in_wr) |->
      (word_IP_DST_LO &&
       !(word_MAC_DA_HI | word_MAC_DASA | word_MAC_SA_LO | word_ETH_IP_VER |
         word_IP_LEN_ID | word_IP_FRAG_TTL_PROTO | word_IP_CHECKSUM_SRC_HI | word_IP_SRC_DST)) ##1
      state==WAIT_EOP)
    else $error("WORD_4 enable: bad outputs or next state");

  assert property (@(posedge clk) disable iff (reset)
    (state==WORD_4 && !in_wr) |=> state==WORD_4)
    else $error("WORD_4 hold violated");

  // WAIT_EOP: no outputs; exit only on ctrl!=0 & in_wr
  assert property (@(posedge clk) disable iff (reset)
    state==WAIT_EOP |-> !(word_MAC_DA_HI | word_MAC_DASA | word_MAC_SA_LO | word_ETH_IP_VER |
                          word_IP_LEN_ID | word_IP_FRAG_TTL_PROTO | word_IP_CHECKSUM_SRC_HI |
                          word_IP_SRC_DST | word_IP_DST_LO))
    else $error("WAIT_EOP: outputs should be 0");

  assert property (@(posedge clk) disable iff (reset)
    (state==WAIT_EOP && in_wr && is_ctrlnz()) |=> state==SKIP_MODULE_HDRS)
    else $error("WAIT_EOP exit violated");

  assert property (@(posedge clk) disable iff (reset)
    (state==WAIT_EOP && !(in_wr && is_ctrlnz())) |=> state==WAIT_EOP)
    else $error("WAIT_EOP hold violated");

  // 4) Output implies state and pair consistency
  // SKIP pair
  assert property (@(posedge clk) disable iff (reset)
    word_MAC_DA_HI |-> (state==SKIP_MODULE_HDRS && in_wr && is_ctrl0() && word_MAC_DASA))
    else $error("word_MAC_DA_HI implication violated");

  assert property (@(posedge clk) disable iff (reset)
    word_MAC_DASA |-> (state==SKIP_MODULE_HDRS && in_wr && is_ctrl0() && word_MAC_DA_HI))
    else $error("word_MAC_DASA implication violated");

  // WORD_1 pair
  assert property (@(posedge clk) disable iff (reset)
    word_MAC_SA_LO |-> (state==WORD_1 && in_wr && word_ETH_IP_VER))
    else $error("word_MAC_SA_LO implication violated");

  assert property (@(posedge clk) disable iff (reset)
    word_ETH_IP_VER |-> (state==WORD_1 && in_wr && word_MAC_SA_LO))
    else $error("word_ETH_IP_VER implication violated");

  // WORD_2 pair
  assert property (@(posedge clk) disable iff (reset)
    word_IP_LEN_ID |-> (state==WORD_2 && in_wr && word_IP_FRAG_TTL_PROTO))
    else $error("word_IP_LEN_ID implication violated");

  assert property (@(posedge clk) disable iff (reset)
    word_IP_FRAG_TTL_PROTO |-> (state==WORD_2 && in_wr && word_IP_LEN_ID))
    else $error("word_IP_FRAG_TTL_PROTO implication violated");

  // WORD_3 pair
  assert property (@(posedge clk) disable iff (reset)
    word_IP_CHECKSUM_SRC_HI |-> (state==WORD_3 && in_wr && word_IP_SRC_DST))
    else $error("word_IP_CHECKSUM_SRC_HI implication violated");

  assert property (@(posedge clk) disable iff (reset)
    word_IP_SRC_DST |-> (state==WORD_3 && in_wr && word_IP_CHECKSUM_SRC_HI))
    else $error("word_IP_SRC_DST implication violated");

  // WORD_4 single
  assert property (@(posedge clk) disable iff (reset)
    word_IP_DST_LO |-> (state==WORD_4 && in_wr))
    else $error("word_IP_DST_LO implication violated");

  // 5) Coverage
  // One clean packet, no stalls
  cover property (@(posedge clk) disable iff (reset)
    state==SKIP_MODULE_HDRS ##1
    (in_wr && is_ctrl0() && word_MAC_DA_HI && word_MAC_DASA) ##1
    (state==WORD_1  && in_wr && word_MAC_SA_LO && word_ETH_IP_VER) ##1
    (state==WORD_2  && in_wr && word_IP_LEN_ID && word_IP_FRAG_TTL_PROTO) ##1
    (state==WORD_3  && in_wr && word_IP_CHECKSUM_SRC_HI && word_IP_SRC_DST) ##1
    (state==WORD_4  && in_wr && word_IP_DST_LO) ##1
    (state==WAIT_EOP && in_wr && is_ctrlnz()) ##1
    state==SKIP_MODULE_HDRS);

  // Packet with arbitrary stalls between words
  sequence stall; !in_wr [*1:$]; endsequence
  cover property (@(posedge clk) disable iff (reset)
    state==SKIP_MODULE_HDRS ##1
    (in_wr && is_ctrl0() && word_MAC_DA_HI && word_MAC_DASA) ##1
    stall ##0 (state==WORD_1  && in_wr && word_MAC_SA_LO && word_ETH_IP_VER) ##1
    stall ##0 (state==WORD_2  && in_wr && word_IP_LEN_ID && word_IP_FRAG_TTL_PROTO) ##1
    stall ##0 (state==WORD_3  && in_wr && word_IP_CHECKSUM_SRC_HI && word_IP_SRC_DST) ##1
    stall ##0 (state==WORD_4  && in_wr && word_IP_DST_LO) ##1
    (state==WAIT_EOP [*1:$]) ##1 (in_wr && is_ctrlnz()) ##1
    state==SKIP_MODULE_HDRS);

endmodule

// Bind into DUT
bind preprocess_control
  preprocess_control_sva #(.DATA_WIDTH(DATA_WIDTH), .CTRL_WIDTH(CTRL_WIDTH)) u_preprocess_control_sva (
    .clk(clk),
    .reset(reset),
    .in_ctrl(in_ctrl),
    .in_wr(in_wr),
    .word_MAC_DA_HI(word_MAC_DA_HI),
    .word_MAC_DASA(word_MAC_DASA),
    .word_MAC_SA_LO(word_MAC_SA_LO),
    .word_ETH_IP_VER(word_ETH_IP_VER),
    .word_IP_LEN_ID(word_IP_LEN_ID),
    .word_IP_FRAG_TTL_PROTO(word_IP_FRAG_TTL_PROTO),
    .word_IP_CHECKSUM_SRC_HI(word_IP_CHECKSUM_SRC_HI),
    .word_IP_SRC_DST(word_IP_SRC_DST),
    .word_IP_DST_LO(word_IP_DST_LO),
    .state(state)
  );