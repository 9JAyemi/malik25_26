// Add this SVA block inside nvme_cq_check (e.g., under `ifndef SYNTHESIS or `ifdef ASSERT_ON)

`ifdef ASSERT_ON
// -------------- Assertions for nvme_cq_check --------------
default clocking cb @(posedge pcie_user_clk); endclocking
default disable iff (!w_cq_rst_n)

// Handy predicates
sequence msi_start_cond;
  (r_cq_msi_irq_head_ptr != r_cq_tail_ptr) && (pcie_msi_en && cq_valid && io_cq_irq_en);
endsequence

// Basic reset wiring
a_rst_and:        assert property (w_cq_rst_n == (pcie_user_rst_n && cq_rst_n));

// State encoding and integrity
a_state_onehot:   assert property ($onehot(cur_state));
a_state_legal:    assert property (cur_state inside {S_IDLE,S_CQ_MSI_IRQ_REQ,S_CQ_MSI_HEAD_SET,S_CQ_MSI_IRQ_TIMER});
a_state_follow:   assert property (!$rose(w_cq_rst_n) |-> (cur_state == $past(next_state)));

// Output/comb correctness
a_msi_req_match:  assert property (cq_msi_irq_req == (cur_state == S_CQ_MSI_IRQ_REQ));
a_legacy_irq_eq:  assert property (cq_legacy_irq_req == ((cq_head_ptr != r_cq_tail_ptr) && (cq_valid && io_cq_irq_en)));

// Registered mirrors
a_tail_is_past:   assert property (!$rose(w_cq_rst_n) |-> (r_cq_tail_ptr == $past(cq_tail_ptr)));

// FSM transitions (1-cycle nexts)
a_idle_stay:      assert property (cur_state==S_IDLE && !msi_start_cond |=> cur_state==S_IDLE);
a_idle_to_req:    assert property (cur_state==S_IDLE &&  msi_start_cond |=> cur_state==S_CQ_MSI_IRQ_REQ);

a_req_stay:       assert property (cur_state==S_CQ_MSI_IRQ_REQ && !cq_msi_irq_ack |=> cur_state==S_CQ_MSI_IRQ_REQ);
a_req_to_head:    assert property (cur_state==S_CQ_MSI_IRQ_REQ &&  cq_msi_irq_ack |=> cur_state==S_CQ_MSI_HEAD_SET);

a_head_to_timer:  assert property (cur_state==S_CQ_MSI_HEAD_SET |=> cur_state==S_CQ_MSI_IRQ_TIMER);

a_timer_to_idle:  assert property (cur_state==S_CQ_MSI_IRQ_TIMER && (r_irq_timer==0)  |=> cur_state==S_IDLE);
a_timer_stay:     assert property (cur_state==S_CQ_MSI_IRQ_TIMER && (r_irq_timer!=0)  |=> cur_state==S_CQ_MSI_IRQ_TIMER);

// Timer behavior
a_timer_load:     assert property (cur_state==S_CQ_MSI_HEAD_SET |=> r_irq_timer == LP_CQ_IRQ_DELAY_TIME);
a_timer_dec:      assert property (cur_state==S_CQ_MSI_IRQ_TIMER |=> r_irq_timer == $past(r_irq_timer) - 8'h01);

// MSI req only when allowed and work pending
a_req_implies_cond: assert property (cq_msi_irq_req |-> (pcie_msi_en && cq_valid && io_cq_irq_en && (r_cq_msi_irq_head_ptr != r_cq_tail_ptr)));

// MSI head pointer updates/holds
a_head_set_load:  assert property (cur_state==S_CQ_MSI_HEAD_SET |=> r_cq_msi_irq_head_ptr == r_cq_tail_ptr);
a_head_idle_load: assert property (cur_state==S_IDLE && !(pcie_msi_en && cq_valid && io_cq_irq_en)
                                   |=> r_cq_msi_irq_head_ptr == r_cq_tail_ptr);
a_head_idle_hold: assert property (cur_state==S_IDLE &&  (pcie_msi_en && cq_valid && io_cq_irq_en)
                                   |=> r_cq_msi_irq_head_ptr == $past(r_cq_msi_irq_head_ptr));
a_head_req_hold:  assert property (cur_state==S_CQ_MSI_IRQ_REQ |=> r_cq_msi_irq_head_ptr == $past(r_cq_msi_irq_head_ptr));
a_head_tmr_hold:  assert property (cur_state==S_CQ_MSI_IRQ_TIMER |=> r_cq_msi_irq_head_ptr == $past(r_cq_msi_irq_head_ptr));

// Async reset effects (next active clock after assertion)
a_reset_state:    assert property ($fell(w_cq_rst_n) |=> cur_state==S_IDLE);
a_reset_headptr:  assert property ($fell(w_cq_rst_n) |=> r_cq_msi_irq_head_ptr==8'h00);

// ------------------- Functional coverage -------------------
c_full_msi_seq: cover property (
  cur_state==S_IDLE && msi_start_cond
  |=> cur_state==S_CQ_MSI_IRQ_REQ ##[1:$] cq_msi_irq_ack
      ##1 cur_state==S_CQ_MSI_HEAD_SET
      ##1 (cur_state==S_CQ_MSI_IRQ_TIMER)
      ##[1:$] (cur_state==S_IDLE)
);

c_timer_load_and_expire: cover property (
  cur_state==S_CQ_MSI_HEAD_SET
  |=> r_irq_timer==LP_CQ_IRQ_DELAY_TIME
      ##1 cur_state==S_CQ_MSI_IRQ_TIMER
      ##[1:$] (cur_state==S_IDLE)
);

c_legacy_irq: cover property (cq_legacy_irq_req);

`endif // ASSERT_ON