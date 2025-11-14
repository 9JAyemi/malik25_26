// SVA bind module for altpcie_pclk_align
// Focus: FSM legality, step/handshake correctness, counters/flags, CDC staging, window_cnt priority/saturation, simple output consts, key coverage

module altpcie_pclk_align_sva;
  // mirror DUT params/states
  localparam int DREG_SIZE = 128;
  localparam INIT = 0, EVAL = 1, ADVC = 2, DELY = 3, BACK = 4, ERR = 5, DONE = 6, MNUL = 7;

  // bind-time implicit connections by name (.* in bind)
  // DUT ports
  logic        rst, clock, PCLK_Master, PCLK_Slave;
  logic [7:0]  offset;
  logic        onestep, onestep_dir;
  logic        PCLK_Master_unused; // placeholder
  logic        PhaseDone;
  logic        PhaseUpDown, PhaseStep, AlignLock;
  logic        PhaseDone_reg, compout_reg;
  logic        pcie_sw_in, pcie_sw_out;

  // DUT internals we check
  logic [3:0]  align_sm;
  logic [DREG_SIZE-1:0] delay_reg;
  logic        all_zero, all_one;
  logic [7:0]  chk_cnt;
  logic        chk_req, chk_ack, chk_ack_r, chk_ack_rr, chk_ok;
  logic        found_zero, found_meta, found_one;
  logic [7:0]  window_cnt;
  logic        clr_window_cnt, inc_window_cnt, dec_window_cnt, half_window_cnt;
  logic [1:0]  retrain_cnt;
  logic        pcie_sw_r, pcie_sw_rr;

  // ---------------------------
  // PCLK_Master domain checks
  // ---------------------------
  // chk_cnt progression and terminal behavior
  assert property (@(posedge PCLK_Master) disable iff (rst)
    chk_cnt != 8'h8f |=> chk_cnt == $past(chk_cnt) + 8'h01);

  assert property (@(posedge PCLK_Master) disable iff (rst)
    (chk_cnt == 8'h8f && chk_req) |=> chk_cnt == 8'h00);

  assert property (@(posedge PCLK_Master) disable iff (rst)
    (chk_cnt == 8'h8f && !chk_req) |=> chk_cnt == 8'h8f);

  // ack reflects MSB of chk_cnt
  assert property (@(posedge PCLK_Master) disable iff (rst)
    chk_ack == chk_cnt[7]);

  // delay_reg shift behavior
  genvar gi;
  generate
    for (gi = 1; gi < DREG_SIZE; gi++) begin : G_SHIFT
      assert property (@(posedge PCLK_Master) disable iff (rst)
        delay_reg[gi] == $past(delay_reg[gi-1]));
    end
  endgenerate
  assert property (@(posedge PCLK_Master) disable iff (rst)
    delay_reg[0] == $past(PCLK_Slave));

  // all_zero/all_one capture at chk_cnt==0x80
  assert property (@(posedge PCLK_Master) disable iff (rst)
    $past(chk_cnt) == 8'h80 |=> all_zero == ~|$past(delay_reg[DREG_SIZE-1:2]));
  assert property (@(posedge PCLK_Master) disable iff (rst)
    $past(chk_cnt) == 8'h80 |=> all_one  ==  & $past(delay_reg[DREG_SIZE-1:2]));

  // pcie_sw 2FF pipeline
  assert property (@(posedge PCLK_Master) disable iff (rst)
    pcie_sw_r  == $past(pcie_sw_in));
  assert property (@(posedge PCLK_Master) disable iff (rst)
    pcie_sw_rr == $past(pcie_sw_r));
  assert property (@(posedge PCLK_Master) disable iff (rst)
    pcie_sw_out == $past(pcie_sw_rr));

  // ---------------------------
  // clock domain checks
  // ---------------------------
  // FSM legal encoding
  assert property (@(posedge clock) disable iff (rst)
    align_sm inside {INIT,EVAL,ADVC,DELY,BACK,ERR,DONE,MNUL});

  // AlignLock behavior: only set in DONE, sticky until reset
  assert property (@(posedge clock) disable iff (rst)
    AlignLock |-> (align_sm == DONE) or $past(AlignLock));
  assert property (@(posedge clock) disable iff (rst)
    $rose(AlignLock) |-> $past(align_sm) == DONE);

  // chk_ack sync staging and chk_ok pulse
  assert property (@(posedge clock) disable iff (rst)
    chk_ack_r  == $past(chk_ack));
  assert property (@(posedge clock) disable iff (rst)
    chk_ack_rr == $past(chk_ack_r));
  assert property (@(posedge clock) disable iff (rst)
    chk_ok |-> (chk_ack_r && !chk_ack_rr) && !$past(chk_ok) ##1 !chk_ok);

  // window_cnt priority and saturation
  // highest priority: clear loads offset
  assert property (@(posedge clock) disable iff (rst)
    clr_window_cnt |=> window_cnt == offset);

  // saturation at 0xFF
  assert property (@(posedge clock) disable iff (rst)
    (window_cnt == 8'hff && !clr_window_cnt) |=> window_cnt == 8'hff);

  // increment when enabled (and not cleared, not saturated)
  assert property (@(posedge clock) disable iff (rst)
    (!clr_window_cnt && inc_window_cnt && $past(window_cnt) != 8'hff)
    |=> window_cnt == $past(window_cnt) + 8'h01);

  // decrement when enabled (only if no higher-priority ops)
  assert property (@(posedge clock) disable iff (rst)
    (!clr_window_cnt && !inc_window_cnt && !half_window_cnt && dec_window_cnt && $past(window_cnt) > 0 && $past(window_cnt) != 8'hff)
    |=> window_cnt == $past(window_cnt) - 8'h01);

  // no underflow on decrement at zero
  assert property (@(posedge clock) disable iff (rst)
    (!clr_window_cnt && !inc_window_cnt && !half_window_cnt && dec_window_cnt && $past(window_cnt) == 8'h00)
    |=> window_cnt == 8'h00);

  // half when enabled (only if no higher-priority ops)
  assert property (@(posedge clock) disable iff (rst)
    (!clr_window_cnt && !inc_window_cnt && !dec_window_cnt && half_window_cnt && $past(window_cnt) != 8'hff)
    |=> window_cnt == {1'b0,$past(window_cnt[7:1])});

  // retrain counter: increment in ERR, saturate at 3
  assert property (@(posedge clock) disable iff (rst)
    (retrain_cnt != 2'b11 && $past(align_sm) == ERR) |=> retrain_cnt == $past(retrain_cnt) + 1);
  assert property (@(posedge clock) disable iff (rst)
    retrain_cnt == 2'b11 |=> retrain_cnt == 2'b11);

  // PhaseStep/PhaseUpDown step lifecycle
  // When entering a move state, PhaseStep stays 1 until PhaseDone==0
  assert property (@(posedge clock) disable iff (rst)
    (align_sm inside {ADVC,DELY,BACK} && PhaseDone != 1'b0) |-> PhaseStep);

  // Completion from move states
  assert property (@(posedge clock) disable iff (rst)
    (align_sm inside {ADVC,DELY,BACK} && PhaseDone == 1'b0)
    |=> !PhaseStep && align_sm == EVAL);

  // Manual one-step behavior from DONE
  assert property (@(posedge clock) disable iff (rst)
    (align_sm == DONE && onestep)
    |=> (align_sm == MNUL && PhaseStep && PhaseUpDown == onestep_dir));
  assert property (@(posedge clock) disable iff (rst)
    (align_sm == MNUL && PhaseDone == 1'b0)
    |=> (!PhaseStep && align_sm == DONE));

  // found_* are cleared in INIT and ERR
  assert property (@(posedge clock) disable iff (rst)
    (align_sm == INIT || align_sm == ERR) |=> (!found_zero && !found_meta && !found_one));

  // outputs tied-low
  assert property (@(posedge clock) PhaseDone_reg == 1'b0 && compout_reg == 1'b0);

  // ---------------------------
  // Coverage (key scenarios)
  // ---------------------------
  cover property (@(posedge clock) disable iff (rst)
    align_sm == DONE && AlignLock);

  cover property (@(posedge clock) disable iff (rst)
    align_sm == ERR ##1 align_sm == INIT);

  cover property (@(posedge clock) disable iff (rst)
    align_sm == DONE && onestep ##1 align_sm == MNUL ##[1:10] (PhaseDone == 1'b0) ##1 align_sm == DONE);

  cover property (@(posedge clock) disable iff (rst)
    align_sm == ADVC);
  cover property (@(posedge clock) disable iff (rst)
    align_sm == DELY);
  cover property (@(posedge clock) disable iff (rst)
    align_sm == BACK);

  cover property (@(posedge clock) disable iff (rst)
    window_cnt == 8'hff);

  cover property (@(posedge clock) disable iff (rst)
    chk_ok);
endmodule

// Bind to DUT (connects by matching names)
bind altpcie_pclk_align altpcie_pclk_align_sva sva_i(.*);