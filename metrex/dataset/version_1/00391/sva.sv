Below is a concise, high-quality SVA block you can paste inside the module (or bind to it) that thoroughly checks key behaviors and provides focused coverage. It assumes no explicit reset, so assertions are disabled during init using $initstate.

`ifdef MC_SVA
  // Defaults
  default clocking cb @ (posedge clk); endclocking
  default disable iff ($initstate);

  // Constant/control outputs
  a_req_ras_const:      assert property (req_ras == 1'b0);
  a_req_cas_const:      assert property (req_cas == 1'b1);
  a_row_cmd_wr_passth:  assert property (row_cmd_wr == act_wait_r);

  // req_data_buf_addr_r updates when idle_r, holds otherwise
  a_dbaddr_cap:   assert property ( idle_r  |=> req_data_buf_addr_r == $past(data_buf_addr));
  a_dbaddr_hold:  assert property (!idle_r  |=> req_data_buf_addr_r == $past(req_data_buf_addr_r));

  // req_periodic_rd_r updates when idle_ns, holds otherwise
  a_prd_cap:      assert property ( idle_ns |=> req_periodic_rd_r == $past(periodic_rd_insert));
  a_prd_hold:     assert property (!idle_ns |=> req_periodic_rd_r == $past(req_periodic_rd_r));

  // req_size_r per BURST_MODE
  if (BURST_MODE == "4") begin
    a_size_bm4_const0:  assert property (req_size_r == 1'b0);
  end
  else if (BURST_MODE == "8") begin
    a_size_bm8_const1:  assert property (req_size_r == 1'b1);
  end
  else if (BURST_MODE == "OTF") begin
    a_size_otf_cap:     assert property ( idle_ns |=> req_size_r == $past(periodic_rd_insert || size));
    a_size_otf_hold:    assert property (!idle_ns |=> req_size_r == $past(req_size_r));
  end

  // req_cmd_r captures when idle_ns, holds otherwise
  a_cmd_cap:      assert property ( idle_ns |=> req_cmd_r == ($past(periodic_rd_insert) ? 3'b001 : $past(cmd)));
  a_cmd_hold:     assert property (!idle_ns |=> req_cmd_r == $past(req_cmd_r));

  // rd_wr_r next-state behavior
  a_rdwr_cap:     assert property ( idle_ns |=> rd_wr_r ==
                                   (((($past(periodic_rd_insert)?3'b001:$past(cmd))[1:0]) == 2'b11) ||
                                      ($past(periodic_rd_insert)?3'b001:$past(cmd))[0]));
  a_rdwr_clr_col: assert property ((!idle_ns &&  sending_col) |=> rd_wr_r == 1'b0);
  a_rdwr_hold:    assert property ((!idle_ns && !sending_col) |=> rd_wr_r == $past(rd_wr_r));

  // req_wr_r next-state behavior
  a_wr_cap:       assert property ( idle_ns |=> req_wr_r ==
                                   (((($past(periodic_rd_insert)?3'b001:$past(cmd))[1:0]) == 2'b11) ||
                                    ~($past(periodic_rd_insert)?3'b001:$past(cmd))[0]));
  a_wr_hold:      assert property (!idle_ns |=> req_wr_r == $past(req_wr_r));

  // Rank capture/hold (parameterized)
  if (RANKS != 1) begin
    a_rank_cap:   assert property ( idle_ns |=> req_rank_r ==
                                   ($past(periodic_rd_insert) ? $past(periodic_rd_rank_r) : $past(rank)));
    a_rank_hold:  assert property (!idle_ns |=> req_rank_r == $past(req_rank_r));
  end else begin
    a_rank_one:   assert property (req_rank_r == {RANK_WIDTH{1'b0}});
  end

  // Bank capture/hold
  a_bank_cap:     assert property ( idle_ns |=> req_bank_r == $past(bank));
  a_bank_hold:    assert property (!idle_ns |=> req_bank_r == $past(req_bank_r));

  // Row capture/hold
  a_row_cap:      assert property ( idle_ns |=> req_row_r == $past(row));
  a_row_hold:     assert property (!idle_ns |=> req_row_r == $past(req_row_r));

  // req_col_r[COL_WIDTH-1:0] capture/hold
  if (COL_WIDTH > 0) begin
    a_col_cap:    assert property ( idle_ns |=> req_col_r[COL_WIDTH-1:0] == $past(col[COL_WIDTH-1:0]));
    a_col_hold:   assert property (!idle_ns |=> req_col_r[COL_WIDTH-1:0] == $past(req_col_r[COL_WIDTH-1:0]));
  end

  // Priority capture/hold
  a_prio_cap:     assert property ( idle_ns |=> req_priority_r == $past(hi_priority));
  a_prio_hold:    assert property (!idle_ns |=> req_priority_r == $past(req_priority_r));

  // Hit/busy logic
  a_rank_hit_def: assert property (rank_hit == (req_rank_r == (periodic_rd_insert ? periodic_rd_rank_r : rank)));
  a_bank_hit_def: assert property (bank_hit == (req_bank_r == bank));
  a_rb_hit_ns:    assert property (rb_hit_busy_ns == (rank_hit && bank_hit && ~idle_ns));
  a_rb_hit_r:     assert property (rb_hit_busy_r == $past(rb_hit_busy_ns));

  // Row hit registered
  a_row_hit_r:    assert property (row_hit_r == $past(req_row_r == row));

  // Maintenance hit definition
  a_maint_hit:    assert property (maint_hit == ((req_rank_r == maint_rank_r) || maint_zq_r || maint_sre_r));

  // col_addr composition (protect with width checks; template is 16b)
  if (ROW_WIDTH > 10 && 10 < 16) a_col_bit10: assert property (col_addr[10] == (auto_pre_r && ~rd_half_rmw));
  if (ROW_WIDTH > 11 && 11 < 16) a_col_bit11: assert property (col_addr[11] == req_col_r[10]);
  if (ROW_WIDTH > 12 && 12 < 16) a_col_bit12: assert property (col_addr[12] == req_size_r);
  if (ROW_WIDTH > 13 && 13 < 16) a_col_bit13: assert property (col_addr[13] == req_col_r[11]);

  generate
    genvar i;
    for (i = 0; i < ROW_WIDTH; i = i + 1) begin: g_col_pass
      if (i < 16 && i < COL_WIDTH && !(i==10 || i==11 || i==12 || i==13)) begin
        a_col_passthrough: assert property (col_addr[i] == req_col_r[i]);
      end
    end
  endgenerate

  // row_addr composition
  a_rowaddr_when_act: assert property ( act_wait_r  |-> row_addr == req_row_r);
  if (ROW_WIDTH > 10) begin
    a_rowaddr_when_not_act:
      assert property (!act_wait_r |-> (row_addr[10] == 1'b0 &&
                                        row_addr[ROW_WIDTH-1:11] == req_row_r[ROW_WIDTH-1:11] &&
                                        row_addr[9:0] == req_row_r[9:0]));
  end else begin
    a_rowaddr_when_not_act_nob10:
      assert property (!act_wait_r |-> row_addr == req_row_r[ROW_WIDTH-1:0]);
  end

  // rank_busy_r correctness
  // Expected next rank index (what req_rank_ns would be)
  function automatic [RANK_WIDTH-1:0] f_next_rank;
    if (RANKS != 1)
      f_next_rank = (idle_ns ? (periodic_rd_insert ? periodic_rd_rank_r : rank) : req_rank_r);
    else
      f_next_rank = {RANK_WIDTH{1'b0}};
  endfunction
  a_rank_busy:
    assert property (rank_busy_r ==
                     ({RANKS{~$past(idle_ns)}} &
                      (ONE[RANKS-1:0] << $past(f_next_rank))));

  // Focused coverage
  c_periodic_hit:      cover property (idle_ns && periodic_rd_insert);
  c_normal_cmd_cap:    cover property (idle_ns && !periodic_rd_insert);
  c_rdwr_cleared:      cover property (!idle_ns && sending_col ##1 (rd_wr_r == 1'b0));
  c_row_rank_bank_hit: cover property ((rank_hit && bank_hit) ##1 row_hit_r);
  if (BURST_MODE == "OTF" && ROW_WIDTH > 12) begin
    c_col_size_bit:    cover property (idle_ns && $changed(req_size_r) ##1 (col_addr[12] == req_size_r));
  end
`endif