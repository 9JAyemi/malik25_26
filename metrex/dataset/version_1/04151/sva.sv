// SVA for INT_MANAGER
// Bind this module to the DUT to check key behaviors and cover main scenarios.

module INT_MANAGER_sva
  #(parameter INT_RST=2'b01, INT_PENDING=2'b10)
(
  input  clk, rst_n, en,

  input  int_en,
  input  rd_int_msk_i, wr_int_msk_i,

  input  rd_req_done_i, wr_req_done_i,

  input  [31:0] int_cnt_o,

  input  msi_on,

  input  cfg_interrupt_rdy_n_i,
  input  cfg_interrupt_legacyclr,
  input  cfg_interrupt_assert_n_o,
  input  cfg_interrupt_n_o,

  // internal DUT signals
  input  rd_int, wr_int,
  input  rd_req_done_prev, wr_req_done_prev,
  input  int_clr,
  input  [1:0] intr_state
);

  // 1) State encoding and reset defaults
  // Allowed encodings only
  assert property (@(posedge clk) (intr_state==INT_RST || intr_state==INT_PENDING));

  // Synchronous reset/enable default values
  assert property (@(posedge clk)
    (!rst_n || !en) |->
      (!rd_int && !wr_int &&
       rd_req_done_prev==1'b0 && wr_req_done_prev==1'b0 &&
       int_clr==1'b0 &&
       cfg_interrupt_assert_n_o==1'b1 && cfg_interrupt_n_o==1'b1 &&
       int_cnt_o==32'b0 &&
       intr_state==INT_RST));

  // 2) Previous-sample flops behave like $past(...)
  assert property (@(posedge clk) disable iff (!rst_n || !en)
    rd_req_done_prev == $past(rd_req_done_i));
  assert property (@(posedge clk) disable iff (!rst_n || !en)
    wr_req_done_prev == $past(wr_req_done_i));

  // 3) Latching of request-done edges into rd_int/wr_int
  assert property (@(posedge clk) disable iff (!rst_n || !en)
    $rose(rd_int) |-> ($rose(rd_req_done_i) && int_en && !rd_int_msk_i && !int_clr));
  assert property (@(posedge clk) disable iff (!rst_n || !en)
    $rose(wr_int) |-> ($rose(wr_req_done_i) && int_en && !wr_int_msk_i && !int_clr));

  // 4) Interrupt clear (int_clr) generation only from valid unmasked edge
  assert property (@(posedge clk) disable iff (!rst_n || !en)
    $rose(int_clr) |-> ($past($rose(rd_req_done_i) && int_en && !rd_int_msk_i) ||
                        $past($rose(wr_req_done_i) && int_en && !wr_int_msk_i)));

  // int_clr pulse is single-cycle and occurs on INT_RST->INT_PENDING
  assert property (@(posedge clk) disable iff (!rst_n || !en)
    $rose(int_clr) |-> (intr_state==INT_PENDING && $past(intr_state)==INT_RST));
  assert property (@(posedge clk) disable iff (!rst_n || !en)
    $rose(int_clr) |=> !int_clr);

  // int_clr clears latched interrupt sources next cycle
  assert property (@(posedge clk) disable iff (!rst_n || !en)
    $rose(int_clr) |=> (!rd_int && !wr_int));

  // int_en low keeps sources cleared
  assert property (@(posedge clk) disable iff (!rst_n || !en)
    !int_en |-> (!rd_int && !wr_int));

  // 5) Output protocol and handshake
  // Outputs are always identical (both active-low together)
  assert property (@(posedge clk)) (cfg_interrupt_assert_n_o == cfg_interrupt_n_o);

  // In INT_PENDING, hold low until ready deasserts low (active-low ready)
  assert property (@(posedge clk) disable iff (!rst_n || !en)
    (intr_state==INT_PENDING && cfg_interrupt_rdy_n_i) |-> (!cfg_interrupt_assert_n_o && !cfg_interrupt_n_o));

  // Ack in INT_PENDING deasserts outputs immediately and returns to INT_RST next cycle
  assert property (@(posedge clk) disable iff (!rst_n || !en)
    (intr_state==INT_PENDING && !cfg_interrupt_rdy_n_i) |-> (cfg_interrupt_assert_n_o && cfg_interrupt_n_o));
  assert property (@(posedge clk) disable iff (!rst_n || !en)
    (intr_state==INT_PENDING && !cfg_interrupt_rdy_n_i) |=> (intr_state==INT_RST));

  // In INT_RST with no new latched source, outputs are high
  assert property (@(posedge clk) disable iff (!rst_n || !en)
    (intr_state==INT_RST && !(rd_int || wr_int)) |-> (cfg_interrupt_assert_n_o && cfg_interrupt_n_o));

  // 6) Counter behavior
  assert property (@(posedge clk) disable iff (!rst_n || !en)
    $rose(int_clr) |-> (int_cnt_o == $past(int_cnt_o)+1));
  assert property (@(posedge clk) disable iff (!rst_n || !en)
    !$rose(int_clr) |-> (int_cnt_o == $past(int_cnt_o)));

  // 7) Coverage
  // Single read interrupt path
  cover property (@(posedge clk) disable iff (!rst_n || !en)
    $rose(rd_req_done_i) && int_en && !rd_int_msk_i ##1 $rose(int_clr));

  // Single write interrupt path
  cover property (@(posedge clk) disable iff (!rst_n || !en)
    $rose(wr_req_done_i) && int_en && !wr_int_msk_i ##1 $rose(int_clr));

  // Simultaneous rd+wr events
  cover property (@(posedge clk) disable iff (!rst_n || !en)
    ($rose(rd_req_done_i) && $rose(wr_req_done_i) && int_en && !rd_int_msk_i && !wr_int_msk_i) ##1 $rose(int_clr));

  // Pending held low then ack
  cover property (@(posedge clk) disable iff (!rst_n || !en)
    $rose(int_clr) ##1 (intr_state==INT_PENDING && cfg_interrupt_rdy_n_i) [*2:$] ##1
    (intr_state==INT_PENDING && !cfg_interrupt_rdy_n_i) ##1 (intr_state==INT_RST));

  // Back-to-back interrupts across an ack
  cover property (@(posedge clk) disable iff (!rst_n || !en)
    $rose(int_clr) ##[1:10] (intr_state==INT_PENDING && !cfg_interrupt_rdy_n_i) ##1 (intr_state==INT_RST) ##[0:5] $rose(int_clr));

  // Optional: exercise unused inputs
  cover property (@(posedge clk) $rose(msi_on));
  cover property (@(posedge clk) $fell(msi_on));
  cover property (@(posedge clk) $rose(cfg_interrupt_legacyclr));

endmodule

// Bind to the DUT
bind INT_MANAGER INT_MANAGER_sva #(.INT_RST(INT_RST), .INT_PENDING(INT_PENDING)) INT_MANAGER_sva_i (
  .clk(clk), .rst_n(rst_n), .en(en),
  .int_en(int_en),
  .rd_int_msk_i(rd_int_msk_i), .wr_int_msk_i(wr_int_msk_i),
  .rd_req_done_i(rd_req_done_i), .wr_req_done_i(wr_req_done_i),
  .int_cnt_o(int_cnt_o),
  .msi_on(msi_on),
  .cfg_interrupt_rdy_n_i(cfg_interrupt_rdy_n_i),
  .cfg_interrupt_legacyclr(cfg_interrupt_legacyclr),
  .cfg_interrupt_assert_n_o(cfg_interrupt_assert_n_o),
  .cfg_interrupt_n_o(cfg_interrupt_n_o),
  .rd_int(rd_int), .wr_int(wr_int),
  .rd_req_done_prev(rd_req_done_prev), .wr_req_done_prev(wr_req_done_prev),
  .int_clr(int_clr),
  .intr_state(intr_state)
);