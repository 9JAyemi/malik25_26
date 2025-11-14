// SVA for mig_7series_v2_0_bank_compare
module mig_7series_v2_0_bank_compare_sva #(
  parameter BANK_WIDTH               = 3,
  parameter TCQ                      = 100,
  parameter BURST_MODE               = "8",
  parameter COL_WIDTH                = 12,
  parameter DATA_BUF_ADDR_WIDTH      = 8,
  parameter ECC                      = "OFF",
  parameter RANK_WIDTH               = 2,
  parameter RANKS                    = 4,
  parameter ROW_WIDTH                = 16
)(
  input  logic                         clk,
  input  logic                         idle_ns,
  input  logic                         idle_r,

  input  logic [DATA_BUF_ADDR_WIDTH-1:0] data_buf_addr,
  input  logic [DATA_BUF_ADDR_WIDTH-1:0] req_data_buf_addr_r,

  input  logic                         periodic_rd_insert,
  input  logic                         req_periodic_rd_r,

  input  logic                         size,
  input  logic                         req_size_r,

  input  logic [2:0]                   cmd,

  input  logic                         sending_col,
  input  logic                         rd_wr_r,
  input  logic                         req_wr_r,

  input  logic [RANK_WIDTH-1:0]        rank,
  input  logic [RANK_WIDTH-1:0]        periodic_rd_rank_r,
  input  logic [RANK_WIDTH-1:0]        req_rank_r,

  input  logic [BANK_WIDTH-1:0]        bank,
  input  logic [BANK_WIDTH-1:0]        req_bank_r,

  input  logic [ROW_WIDTH-1:0]         row,
  input  logic [ROW_WIDTH-1:0]         req_row_r,

  input  logic [COL_WIDTH-1:0]         col,
  input  logic [ROW_WIDTH-1:0]         col_addr,

  input  logic                         hi_priority,
  input  logic                         req_priority_r,

  input  logic [RANK_WIDTH-1:0]        maint_rank_r,
  input  logic                         maint_zq_r,
  input  logic                         maint_sre_r,
  input  logic                         maint_hit,

  input  logic                         rb_hit_busy_ns,
  input  logic                         rb_hit_busy_r,
  input  logic                         row_hit_r,

  input  logic                         req_ras,
  input  logic                         req_cas,
  input  logic                         row_cmd_wr,
  input  logic                         act_wait_r,

  input  logic [ROW_WIDTH-1:0]         row_addr,

  input  logic                         auto_pre_r,
  input  logic                         rd_half_rmw,

  input  logic [RANKS-1:0]             rank_busy_r
);

  default clocking @(posedge clk); endclocking

  // req_data_buf_addr_r updates only when idle_r; else holds
  assert property ( idle_r  |-> ##1 req_data_buf_addr_r == $past(data_buf_addr) );
  assert property ( !idle_r |-> ##1 req_data_buf_addr_r == $past(req_data_buf_addr_r) );

  // req_periodic_rd_r update/hold on idle_ns
  assert property ( idle_ns  |-> ##1 req_periodic_rd_r == $past(periodic_rd_insert) );
  assert property ( !idle_ns |-> ##1 req_periodic_rd_r == $past(req_periodic_rd_r) );

  // req_size_r behavior per BURST_MODE
  generate
    if (BURST_MODE == "4") begin
      assert property ( req_size_r == 1'b0 );
    end else if (BURST_MODE == "8") begin
      assert property ( req_size_r == 1'b1 );
    end else if (BURST_MODE == "OTF") begin
      assert property ( idle_ns  |-> ##1 req_size_r == $past(periodic_rd_insert || size) );
      assert property ( !idle_ns |-> ##1 req_size_r == $past(req_size_r) );
    end
  endgenerate

  // rd_wr_r / req_wr_r decode on idle_ns
  assert property ( idle_ns &&  periodic_rd_insert
                    |-> ##1 (rd_wr_r == 1'b1 && req_wr_r == 1'b0) );

  assert property ( idle_ns && !periodic_rd_insert
                    |-> ##1 ( rd_wr_r == (($past(cmd)[1:0] == 2'b11) || $past(cmd)[0]) &&
                               req_wr_r == (($past(cmd)[1:0] == 2'b11) || ~($past(cmd)[0])) ) );

  // rd_wr_r hold/clear when !idle_ns
  assert property ( !idle_ns && !sending_col |-> ##1 rd_wr_r == $past(rd_wr_r) );
  assert property ( !idle_ns &&  sending_col |-> ##1 rd_wr_r == 1'b0 );

  // req_wr_r holds when !idle_ns
  assert property ( !idle_ns |-> ##1 req_wr_r == $past(req_wr_r) );

  // req_rank_r update/hold when RANKS != 1
  generate if (RANKS != 1) begin
    assert property ( idle_ns  |-> ##1 req_rank_r == $past(periodic_rd_insert ? periodic_rd_rank_r : rank) );
    assert property ( !idle_ns |-> ##1 req_rank_r == $past(req_rank_r) );
  end endgenerate

  // req_bank_r, req_row_r update/hold on idle_ns
  assert property ( idle_ns  |-> ##1 req_bank_r == $past(bank) );
  assert property ( !idle_ns |-> ##1 req_bank_r == $past(req_bank_r) );

  assert property ( idle_ns  |-> ##1 req_row_r == $past(row) );
  assert property ( !idle_ns |-> ##1 req_row_r == $past(req_row_r) );

  // row_hit and rb_hit_busy
  assert property ( row_hit_r == $past(req_row_r == row) );

  assert property ( rb_hit_busy_ns ==
                    ((req_rank_r == (periodic_rd_insert ? periodic_rd_rank_r : rank)) &&
                     (req_bank_r == bank) && ~idle_ns) );

  assert property ( rb_hit_busy_r == $past(rb_hit_busy_ns) );

  // maint_hit
  assert property ( maint_hit ==
                    ((req_rank_r == maint_rank_r) || maint_zq_r || maint_sre_r) );

  // req_priority_r update/hold on idle_ns
  assert property ( idle_ns  |-> ##1 req_priority_r == $past(hi_priority) );
  assert property ( !idle_ns |-> ##1 req_priority_r == $past(req_priority_r) );

  // req_ras/req_cas constants; row_cmd_wr mirrors act_wait_r
  assert property ( req_ras == 1'b0 );
  assert property ( req_cas == 1'b1 );
  assert property ( row_cmd_wr == act_wait_r );

  // row_addr mapping
  assert property ( act_wait_r  |-> (row_addr == req_row_r) );
  generate if (ROW_WIDTH > 10) begin
    assert property ( !act_wait_r |-> (row_addr[10] == 1'b0) );
  end endgenerate

  // col_addr mapping (check key modified bits)
  generate
    if (ROW_WIDTH > 10) begin
      assert property ( col_addr[10] == (auto_pre_r && ~rd_half_rmw) );
    end
    if (ROW_WIDTH > 11) begin
      assert property ( $past(idle_ns) |-> (col_addr[11] == $past(col[10])) );
    end
    if (ROW_WIDTH > 12) begin
      assert property ( col_addr[12] == req_size_r );
    end
    if (ROW_WIDTH > 13) begin
      assert property ( $past(idle_ns) |-> (col_addr[13] == $past(col[11])) );
    end
  endgenerate

  // rank_busy_r behavior
  localparam [RANKS-1:0] ONE_HOT_BASE = { {RANKS-1{1'b0}}, 1'b1 };
  assert property ( $past(idle_ns)  |-> (rank_busy_r == {RANKS{1'b0}}) );
  assert property ( !$past(idle_ns) |-> (rank_busy_r == (ONE_HOT_BASE << $past(req_rank_r))) );

  // Coverage (concise)
  cover property ( idle_ns &&  periodic_rd_insert ##1 (rd_wr_r && !req_wr_r) );
  cover property ( idle_ns && !periodic_rd_insert && (cmd[1:0]==2'b11) ##1 (rd_wr_r && req_wr_r) );
  cover property ( idle_ns && !periodic_rd_insert &&  cmd[0] ##1 ( rd_wr_r && !req_wr_r) );
  cover property ( idle_ns && !periodic_rd_insert && !cmd[0] ##1 (!rd_wr_r &&  req_wr_r) );
  cover property ( !idle_ns && sending_col ##1 (rd_wr_r==0) );
  cover property ( maint_zq_r && maint_hit );
  cover property ( (req_rank_r == (periodic_rd_insert ? periodic_rd_rank_r : rank)) &&
                   (req_bank_r == bank) && !idle_ns && rb_hit_busy_ns );
  cover property ( !act_wait_r && (ROW_WIDTH>10) && (row_addr[10]==0) );
  cover property ( (ROW_WIDTH>10) && auto_pre_r && !rd_half_rmw && col_addr[10] );

endmodule

bind mig_7series_v2_0_bank_compare
  mig_7series_v2_0_bank_compare_sva #(
    .BANK_WIDTH(BANK_WIDTH),
    .TCQ(TCQ),
    .BURST_MODE(BURST_MODE),
    .COL_WIDTH(COL_WIDTH),
    .DATA_BUF_ADDR_WIDTH(DATA_BUF_ADDR_WIDTH),
    .ECC(ECC),
    .RANK_WIDTH(RANK_WIDTH),
    .RANKS(RANKS),
    .ROW_WIDTH(ROW_WIDTH)
  ) mig_7series_v2_0_bank_compare_sva_i (.*);