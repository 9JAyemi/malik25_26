// SVA for ui_cmd
// Drop inside the module or bind to it with ASSERT_ON defined.

`ifdef ASSERT_ON
// Default clock
default clocking cb @(posedge clk); endclocking

// Ready generation (one-cycle pipe of accept_ns && !rd_buf_full && !wr_req_16)
assert property (disable iff (rst) (accept_ns && !rd_buf_full && !wr_req_16) |=> app_rdy);
assert property (disable iff (rst) app_rdy |-> $past(accept_ns && !rd_buf_full && !wr_req_16));

// app_en clears under reset and stays low while rst
assert property (rst |-> (!app_en_ns1 && !app_en_ns2));
assert property (rst |=> (!app_en_r1 && !app_en_r2));

// Pipelining: cmd/sz/hi_pri/en shift when app_rdy, hold otherwise
assert property (disable iff (rst) app_rdy |=> (app_cmd_r1 == $past(app_cmd)     && app_cmd_r2     == $past(app_cmd_r1)));
assert property (disable iff (rst) !app_rdy |=> (app_cmd_r1 == $past(app_cmd_r1) && app_cmd_r2     == $past(app_cmd_r2)));
assert property (disable iff (rst) app_rdy |=> (app_sz_r1  == $past(app_sz)      && app_sz_r2      == $past(app_sz_r1)));
assert property (disable iff (rst) !app_rdy |=> (app_sz_r1  == $past(app_sz_r1)  && app_sz_r2      == $past(app_sz_r2)));
assert property (disable iff (rst) app_rdy |=> (app_hi_pri_r1 == $past(app_hi_pri) && app_hi_pri_r2 == $past(app_hi_pri_r1)));
assert property (disable iff (rst) !app_rdy |=> (app_hi_pri_r1 == $past(app_hi_pri_r1) && app_hi_pri_r2 == $past(app_hi_pri_r2)));
assert property (disable iff (rst) app_rdy |=> (app_en_r1  == $past(app_en)      && app_en_r2      == $past(app_en_r1)));
assert property (disable iff (rst) !app_rdy |=> (app_en_r1  == $past(app_en_r1)  && app_en_r2      == $past(app_en_r2)));

// Address pipeline: r1 updates only on (app_rdy && app_en); r2 updates on app_rdy
assert property (disable iff (rst) (app_rdy && app_en) |=> app_addr_r1 == $past(app_addr));
assert property (disable iff (rst) (!app_rdy || !app_en) |=> app_addr_r1 == $past(app_addr_r1));
assert property (disable iff (rst) app_rdy |=> app_addr_r2 == $past(app_addr_r1));
assert property (disable iff (rst) !app_rdy |=> app_addr_r2 == $past(app_addr_r2));

// Output selection from the proper stage
assert property (app_rdy  -> col == app_addr_r1[0+:COL_WIDTH]);
assert property (!app_rdy -> col == app_addr_r2[0+:COL_WIDTH]);

generate
  if (MEM_ADDR_ORDER == "ROW_BANK_COLUMN") begin
    assert property (app_rdy  -> row  == app_addr_r1[COL_WIDTH+BANK_WIDTH +: ROW_WIDTH]);
    assert property (!app_rdy -> row  == app_addr_r2[COL_WIDTH+BANK_WIDTH +: ROW_WIDTH]);
    assert property (app_rdy  -> bank == app_addr_r1[COL_WIDTH +: BANK_WIDTH]);
    assert property (!app_rdy -> bank == app_addr_r2[COL_WIDTH +: BANK_WIDTH]);
  end else begin
    assert property (app_rdy  -> row  == app_addr_r1[COL_WIDTH +: ROW_WIDTH]);
    assert property (!app_rdy -> row  == app_addr_r2[COL_WIDTH +: ROW_WIDTH]);
    assert property (app_rdy  -> bank == app_addr_r1[COL_WIDTH+ROW_WIDTH +: BANK_WIDTH]);
    assert property (!app_rdy -> bank == app_addr_r2[COL_WIDTH+ROW_WIDTH +: BANK_WIDTH]);
  end
endgenerate

generate
  if (RANKS == 1) begin
    assert property (rank == {RANK_WIDTH{1'b0}});
  end else begin
    assert property (app_rdy  -> rank == app_addr_r1[COL_WIDTH+ROW_WIDTH+BANK_WIDTH +: RANK_WIDTH]);
    assert property (!app_rdy -> rank == app_addr_r2[COL_WIDTH+ROW_WIDTH+BANK_WIDTH +: RANK_WIDTH]);
  end
endgenerate

assert property (app_rdy  -> size == app_sz_r1);
assert property (!app_rdy -> size == app_sz_r2);
assert property (app_rdy  -> cmd  == app_cmd_r1);
assert property (!app_rdy -> cmd  == app_cmd_r2);
assert property (app_rdy  -> hi_priority == app_hi_pri_r1);
assert property (!app_rdy -> hi_priority == app_hi_pri_r2);

// use_addr and accept
assert property (use_addr == (app_en_r2 && app_rdy));
assert property (rd_accepted == (use_addr && app_rdy && (app_cmd_r2[1:0] == 2'b01)));
assert property (wr_accepted == (use_addr && app_rdy && ((app_cmd_r2[1:0] == 2'b00) || (app_cmd_r2[1:0] == 2'b11))));

// Data buffer address selection
assert property (((app_cmd_r2[1:0] == 2'b00) || (app_cmd_r2[1:0] == 2'b11)) -> data_buf_addr == wr_data_buf_addr);
assert property (!((app_cmd_r2[1:0] == 2'b00) || (app_cmd_r2[1:0] == 2'b11)) -> data_buf_addr == rd_data_buf_addr_r);

// Sanity on acceptance and no-X when accepting
assert property (rd_accepted -> (data_buf_addr == rd_data_buf_addr_r));
assert property (wr_accepted -> (data_buf_addr == wr_data_buf_addr));
assert property (disable iff (rst) (use_addr && app_rdy) |-> !$isunknown({cmd,size,hi_priority,rank,bank,row,col}));

// Minimal coverage
cover property (disable iff (rst) (accept_ns && !rd_buf_full && !wr_req_16) ##1 app_rdy);
cover property (disable iff (rst) rd_accepted);
cover property (disable iff (rst) wr_accepted && (app_cmd_r2[1:0] == 2'b00));
cover property (disable iff (rst) wr_accepted && (app_cmd_r2[1:0] == 2'b11));
cover property (disable iff (rst) app_rdy ##1 !app_rdy);
`endif