// SVA for nfa_get_finals
// Bind into DUT to access internals without extra wiring.
bind nfa_get_finals nfa_get_finals_sva i_nfa_get_finals_sva();

module nfa_get_finals_sva;

  // Local copies of FSM encodings (width-normalized)
  localparam logic [1:0] STG0 = 2'b10; // ap_ST_pp0_stg0_fsm_0
  localparam logic [1:0] STG1 = 2'b00; // ap_ST_pp0_stg1_fsm_1
  localparam logic [1:0] STG2 = 2'b01; // ap_ST_pp0_stg2_fsm_2 (normalized from 1'b1)
  localparam logic [1:0] STG3 = 2'b11; // ap_ST_pp0_stg3_fsm_3

  default clocking cb @(posedge ap_clk); endclocking
  default disable iff (ap_rst);

  // -------------------------
  // Basic sanity / reset / encodings
  // -------------------------
  // During reset, FSM must be in STG0
  assert property (ap_rst |-> ap_CS_fsm == STG0);

  // FSM must always be in a legal encoding
  assert property (ap_CS_fsm inside {STG0, STG1, STG2, STG3});

  // Allowed next-state transitions only
  assert property ($past(ap_CS_fsm)==STG0 |-> ap_CS_fsm inside {STG0, STG1});
  assert property ($past(ap_CS_fsm)==STG1 |-> ap_CS_fsm inside {STG1, STG2, STG0});
  assert property ($past(ap_CS_fsm)==STG2 |-> ap_CS_fsm inside {STG2, STG3});
  assert property ($past(ap_CS_fsm)==STG3 |-> ap_CS_fsm inside {STG3, STG0});

  // Critical outputs never X
  assert property (!$isunknown({ap_done, ap_idle, ap_ready,
                                nfa_finals_buckets_req_write,
                                nfa_finals_buckets_rsp_read})));

  // Constant outputs
  assert property (nfa_finals_buckets_dataout == 32'h0000_0000);
  assert property (nfa_finals_buckets_req_din  == 1'b0);
  assert property (nfa_finals_buckets_size     == 32'h0000_0001);

  // ap_return_1 reflects datain combinationally
  assert property (ap_return_1 == nfa_finals_buckets_datain);

  // -------------------------
  // Handshake/control equivalences
  // -------------------------
  // READY
  assert property (ap_ready == (ap_reg_ppiten_pp0_it0 && ap_ce && (ap_CS_fsm==STG3)));

  // IDLE
  assert property (ap_idle == ((ap_CS_fsm==STG0) && !ap_start && !ap_reg_ppiten_pp0_it0 && !ap_reg_ppiten_pp0_it1));

  // DONE: two legal causes, no others
  localparam bit ONE = 1'b1;
  localparam bit ZERO = 1'b0;
  wire done_c0 = (ap_CS_fsm==STG0) && ap_reg_ppiten_pp0_it0 && !ap_start;
  wire done_c1 = (ap_CS_fsm==STG1) && ap_reg_ppiten_pp0_it1 && ap_ce && nfa_finals_buckets_rsp_empty_n;
  assert property (ap_done == (done_c0 || done_c1));

  // REQ_WRITE: exactly two legal causes
  wire wr_c0 = (ap_reg_ppiten_pp0_it0 && ap_ce && (ap_CS_fsm==STG3));
  wire wr_c1 = ((ap_CS_fsm==STG0) && ap_reg_ppiten_pp0_it0 && ap_ce && ap_start);
  assert property (nfa_finals_buckets_req_write == (wr_c0 || wr_c1));

  // RSP_READ: equivalence
  wire rd_c0 = (ap_ce && nfa_finals_buckets_rsp_empty_n && (ap_CS_fsm==STG2) && ap_reg_ppiten_pp0_it0);
  wire rd_c1 = (ap_ce && nfa_finals_buckets_rsp_empty_n && (ap_CS_fsm==STG1) && ap_reg_ppiten_pp0_it1);
  assert property (nfa_finals_buckets_rsp_read == (rd_c0 || rd_c1));

  // No read when empty
  assert property (!nfa_finals_buckets_rsp_empty_n |-> !nfa_finals_buckets_rsp_read);

  // Idle and ready are mutually exclusive
  assert property (!(ap_idle && ap_ready));

  // -------------------------
  // Address/write checks
  // -------------------------
  // When writing in STG0, address must be 0
  assert property (nfa_finals_buckets_req_write && (ap_CS_fsm==STG0) |-> nfa_finals_buckets_address == 32'h0000_0000);

  // When writing in STG3, address must be 1
  assert property (nfa_finals_buckets_req_write && (ap_CS_fsm==STG3) |-> nfa_finals_buckets_address == 32'h0000_0001);

  // Address must be known when a write occurs
  assert property (nfa_finals_buckets_req_write |-> !$isunknown(nfa_finals_buckets_address));

  // -------------------------
  // Data capture timing
  // -------------------------
  // Capture in STG2: ap_return_0 reflects datain on next cycle after a read
  assert property (rd_c0 |-> ##1 ap_return_0 == $past(nfa_finals_buckets_datain));

  // -------------------------
  // Useful coverage
  // -------------------------
  // Cover: full request->read->read->response path
  cover property (
    (ap_CS_fsm==STG0 && ap_ce && ap_start && ap_reg_ppiten_pp0_it0 && nfa_finals_buckets_req_write && nfa_finals_buckets_address==32'h0)
    ##[1:$] (ap_CS_fsm==STG1 && nfa_finals_buckets_rsp_empty_n && ap_ce && nfa_finals_buckets_rsp_read)
    ##[1:$] (ap_CS_fsm==STG2 && nfa_finals_buckets_rsp_empty_n && ap_ce && nfa_finals_buckets_rsp_read)
    ##[1:$] (ap_CS_fsm==STG3 && ap_ce && ap_reg_ppiten_pp0_it0 && nfa_finals_buckets_req_write && nfa_finals_buckets_address==32'h1 && ap_ready)
  );

  // Cover: DONE via STG1 path
  cover property (ap_CS_fsm==STG1 && ap_ce && ap_reg_ppiten_pp0_it1 && nfa_finals_buckets_rsp_empty_n ##0 ap_done);

  // Cover: DONE via STG0 path (start low tail)
  cover property (ap_CS_fsm==STG0 && ap_reg_ppiten_pp0_it0 && !ap_start ##0 ap_done);

  // Cover: stall on empty in STG1 or STG2
  cover property ((ap_CS_fsm inside {STG1,STG2}) && ap_ce && !nfa_finals_buckets_rsp_empty_n && !nfa_finals_buckets_rsp_read);

endmodule