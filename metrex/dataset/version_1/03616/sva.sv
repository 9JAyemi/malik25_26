// SVA checker for ic_download. Bind into all instances of the DUT.
module ic_download_sva
(
  input  logic         clk,
  input  logic         rst,
  input  logic [15:0]  rep_flit_ic,
  input  logic         v_rep_flit_ic,
  input  logic [1:0]   rep_ctrl_ic,
  input  logic [127:0] mem_flits_ic,
  input  logic         v_mem_flits_ic,
  input  logic [1:0]   ic_download_state,
  input  logic [127:0] inst_word_ic,
  input  logic         v_inst_word,

  // internal control signals (bound from DUT scope)
  input  logic         en_mem_flits_ic,
  input  logic         en_rep_flit_ic,
  input  logic         inc_cnt,
  input  logic         fsm_rst,
  input  logic [2:0]   cnt,
  input  logic [7:0]   en_instword
);

  localparam logic [1:0] IDLE = 2'b00;
  localparam logic [1:0] BUSY = 2'b01;
  localparam logic [1:0] RDY  = 2'b10;

  default clocking cb @ (posedge clk); endclocking
  default disable iff (rst);

  // Legal states only
  assert property (ic_download_state inside {IDLE, BUSY, RDY});

  // Reset effects (checked one cycle after rst deassertion begins)
  assert property ($rose(rst) ##1 (ic_download_state==IDLE && v_inst_word==1'b0 && inst_word_ic==128'h0 && cnt==3'b000));

  // v_inst_word only and exactly in RDY
  assert property (v_inst_word == (ic_download_state==RDY));

  // RDY is a single-cycle terminal: RDY -> next IDLE, with fsm_rst asserted in RDY
  assert property (ic_download_state==RDY |-> fsm_rst);
  assert property (ic_download_state==RDY |=> ic_download_state==IDLE);
  // RDY cycle causes clear on next edge
  assert property (ic_download_state==RDY |=> (inst_word_ic==128'h0 && cnt==3'b000));

  // Priority in IDLE: mem beats rep
  assert property (ic_download_state==IDLE && v_mem_flits_ic && v_rep_flit_ic
                   |-> en_mem_flits_ic && !en_rep_flit_ic);
  // IDLE transitions
  assert property (ic_download_state==IDLE && v_mem_flits_ic
                   |=> ic_download_state==RDY);
  assert property (ic_download_state==IDLE && !v_mem_flits_ic && v_rep_flit_ic
                   |=> ic_download_state==BUSY);
  assert property (ic_download_state==IDLE && !v_mem_flits_ic && !v_rep_flit_ic
                   |=> ic_download_state==IDLE);

  // BUSY transitions and controls
  assert property (ic_download_state==BUSY && rep_ctrl_ic==2'b11
                   |-> en_rep_flit_ic && !inc_cnt);
  assert property (ic_download_state==BUSY && rep_ctrl_ic==2'b11
                   |=> ic_download_state==RDY);
  assert property (ic_download_state==BUSY && rep_ctrl_ic==2'b10
                   |-> en_rep_flit_ic && inc_cnt);
  assert property (ic_download_state==BUSY && rep_ctrl_ic==2'b10
                   |=> ic_download_state==BUSY);
  assert property (ic_download_state==BUSY && !(rep_ctrl_ic inside {2'b10,2'b11})
                   |-> !en_rep_flit_ic && !inc_cnt);
  assert property (ic_download_state==BUSY && !(rep_ctrl_ic inside {2'b10,2'b11})
                   |=> ic_download_state==BUSY);

  // Enables only where intended
  assert property (en_mem_flits_ic |-> (ic_download_state==IDLE && v_mem_flits_ic));
  assert property (en_rep_flit_ic |-> ( (ic_download_state==IDLE && v_rep_flit_ic) ||
                                        (ic_download_state==BUSY && (rep_ctrl_ic inside {2'b10,2'b11})) ));
  // Never assert both enables
  assert property (!(en_mem_flits_ic && en_rep_flit_ic));

  // cnt behavior
  assert property (inc_cnt |-> (ic_download_state==BUSY && rep_ctrl_ic==2'b10));
  assert property (ic_download_state==BUSY && rep_ctrl_ic==2'b10 |-> inc_cnt);
  assert property (inc_cnt |=> cnt == $past(cnt)+3'b001);

  // mem load: full 128b transfer
  assert property (ic_download_state==IDLE && v_mem_flits_ic
                   |=> ic_download_state==RDY && inst_word_ic == $past(mem_flits_ic));

  // No writes without enables
  assert property (!en_mem_flits_ic && !en_rep_flit_ic && !fsm_rst |=> $stable(inst_word_ic));

  // Rep path write gating: only selected 16b lanes may change
  genvar i;
  generate
    for (i=0; i<8; i++) begin : g_lane_gate
      assert property ((!en_mem_flits_ic && en_rep_flit_ic)
                       |=> ( en_instword[i] || !$changed(inst_word_ic[i*16 +: 16]) ));
    end
  endgenerate

  // en_instword decode must match cnt
  function automatic logic [7:0] expected_en(input logic [2:0] c);
    case (c)
      3'b000: expected_en = 8'b00000001;
      3'b001: expected_en = 8'b00000010;
      3'b010: expected_en = 8'b00000100;
      3'b011: expected_en = 8'b00001000;
      3'b100: expected_en = 8'b00010000;
      3'b101: expected_en = 8'b00100001;
      3'b110: expected_en = 8'b01000001;
      3'b111: expected_en = 8'b10000001;
      default: expected_en = 8'b00000000;
    endcase
  endfunction
  assert property (en_instword == expected_en(cnt));

  // Coverage
  cover property (ic_download_state==IDLE);
  cover property (ic_download_state==BUSY);
  cover property (ic_download_state==RDY);
  cover property (ic_download_state==IDLE && v_mem_flits_ic
                  ##1 ic_download_state==RDY ##1 ic_download_state==IDLE);
  cover property (ic_download_state==IDLE && !v_mem_flits_ic && v_rep_flit_ic);
  sequence rep_fill_seq;
    (ic_download_state==IDLE && v_rep_flit_ic && !v_mem_flits_ic) ##1
    (ic_download_state==BUSY && rep_ctrl_ic==2'b10)[*1:$] ##1
    (ic_download_state==BUSY && rep_ctrl_ic==2'b11) ##1
    (ic_download_state==RDY);
  endsequence
  cover property (rep_fill_seq);
  cover property (cnt==3'b111);
  cover property (ic_download_state==IDLE && v_mem_flits_ic && v_rep_flit_ic);

endmodule

// Bind the checker into the DUT. Connect internal signals by name.
bind ic_download ic_download_sva u_ic_download_sva (
  .clk               (clk),
  .rst               (rst),
  .rep_flit_ic       (rep_flit_ic),
  .v_rep_flit_ic     (v_rep_flit_ic),
  .rep_ctrl_ic       (rep_ctrl_ic),
  .mem_flits_ic      (mem_flits_ic),
  .v_mem_flits_ic    (v_mem_flits_ic),
  .ic_download_state (ic_download_state),
  .inst_word_ic      (inst_word_ic),
  .v_inst_word       (v_inst_word),

  .en_mem_flits_ic   (en_mem_flits_ic),
  .en_rep_flit_ic    (en_rep_flit_ic),
  .inc_cnt           (inc_cnt),
  .fsm_rst           (fsm_rst),
  .cnt               (cnt),
  .en_instword       (en_instword)
);