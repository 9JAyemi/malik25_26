Below is a concise SVA bind module that checks key functionality and adds targeted coverage. It only depends on DUT ports (it mirrors the few internal latches it needs). Bind it to the DUT for your simulation/formal runs.


// SVA for mig_7series_v1_9_bank_compare
module mig_7series_v1_9_bank_compare_sva #(
  parameter BANK_WIDTH               = 3,
  parameter TCQ = 100,
  parameter BURST_MODE               = "8",
  parameter COL_WIDTH                = 12,
  parameter DATA_BUF_ADDR_WIDTH      = 8,
  parameter ECC                      = "OFF",
  parameter RANK_WIDTH               = 2,
  parameter RANKS                    = 4,
  parameter ROW_WIDTH                = 16
)(
  input clk,
  input idle_ns,
  input idle_r,

  // buf addr
  input  [DATA_BUF_ADDR_WIDTH-1:0] data_buf_addr,
  input  [DATA_BUF_ADDR_WIDTH-1:0] req_data_buf_addr_r,

  // periodic
  input periodic_rd_insert,
  input req_periodic_rd_r,

  // size/BURST_MODE
  input size,
  input req_size_r,

  // command and decode
  input [2:0] cmd,
  input rd_wr_r,
  input req_wr_r,
  input sending_col,

  // rank/bank/row/col
  input [RANK_WIDTH-1:0] rank,
  input [RANK_WIDTH-1:0] periodic_rd_rank_r,
  input [RANK_WIDTH-1:0] req_rank_r,

  input [BANK_WIDTH-1:0] bank,
  input [BANK_WIDTH-1:0] req_bank_r,

  input [ROW_WIDTH-1:0] row,
  input [ROW_WIDTH-1:0] req_row_r,

  input [COL_WIDTH-1:0] col,
  input [ROW_WIDTH-1:0] col_addr,

  // priority
  input hi_priority,
  input req_priority_r,

  // maint
  input [RANK_WIDTH-1:0] maint_rank_r,
  input maint_zq_r,
  input maint_sre_r,
  input maint_hit,

  // col/row modifiers
  input auto_pre_r,
  input rd_half_rmw,

  // CAS/RAS/row_cmd_wr
  input req_ras,
  input req_cas,
  input row_cmd_wr,
  input act_wait_r,

  // row addr out
  input [ROW_WIDTH-1:0] row_addr,

  // hit/busy
  input rb_hit_busy_ns,
  input rb_hit_busy_r,

  // rank busy
  input [RANKS-1:0] rank_busy_r
);

  default clocking cb @(posedge clk); endclocking

  // Mirror the latched column (matches DUT req_col_r behavior)
  logic [COL_WIDTH-1:0] f_col_q;
  always_ff @(posedge clk) begin
    if (idle_ns) f_col_q <= col;
  end

  // Common helpers
  function automatic bit exp_rd_wr(input bit pdi, input [2:0] c);
    exp_rd_wr = pdi ? 1'b1 : ((c[1:0] == 2'b11) || c[0]);
  endfunction
  function automatic bit exp_req_wr(input bit pdi, input [2:0] c);
    exp_req_wr = pdi ? 1'b0 : ((c[1:0] == 2'b11) || ~c[0]);
  endfunction

  //============================
  // Gating/update semantics
  //============================

  // req_data_buf_addr_r updates on idle_r, else holds
  assert property (idle_r |=> req_data_buf_addr_r == $past(data_buf_addr));
  assert property (!idle_r |=> req_data_buf_addr_r == $past(req_data_buf_addr_r));

  // req_periodic_rd_r updates on idle_ns, else holds
  assert property (idle_ns |=> req_periodic_rd_r == $past(periodic_rd_insert));
  assert property (!idle_ns |=> $stable(req_periodic_rd_r));

  // req_size_r behavior per BURST_MODE
  generate
    if (BURST_MODE == "4") begin
      assert property (1'b1 |-> (req_size_r == 1'b0));
      cover property (req_size_r == 1'b0);
    end else if (BURST_MODE == "8") begin
      assert property (1'b1 |-> (req_size_r == 1'b1));
      cover property (req_size_r == 1'b1);
    end else if (BURST_MODE == "OTF") begin
      assert property (idle_ns |=> req_size_r == $past(periodic_rd_insert || size));
      assert property (!idle_ns |=> $stable(req_size_r));
      cover property (idle_ns ##1 req_size_r);
      cover property (idle_ns ##1 !req_size_r);
    end
  endgenerate

  // rd_wr_r / req_wr_r decode on idle_ns; hold/monotonic while busy
  assert property (idle_ns |=> rd_wr_r == exp_rd_wr($past(periodic_rd_insert), $past(cmd)));
  assert property (idle_ns |=> req_wr_r == exp_req_wr($past(periodic_rd_insert), $past(cmd)));
  // req_wr holds when not idle
  assert property (!idle_ns |=> $stable(req_wr_r));
  // rd_wr holds unless cleared by sending_col; never rises while busy
  assert property (!idle_ns &&  sending_col &&  rd_wr_r |=> !rd_wr_r);
  assert property (!idle_ns && !sending_col            |=> rd_wr_r == $past(rd_wr_r));
  assert property (!idle_ns && !rd_wr_r                |=> !rd_wr_r);

  // req_rank_r update (only meaningful when RANKS!=1)
  generate if (RANKS != 1) begin
    assert property (idle_ns |=> req_rank_r == $past(periodic_rd_insert ? periodic_rd_rank_r : rank));
    assert property (!idle_ns |=> req_rank_r == $past(req_rank_r));
    // range check
    assert property (1'b1 |-> (req_rank_r < RANKS));
  end endgenerate

  // req_bank_r update
  assert property (idle_ns |=> req_bank_r == $past(bank));
  assert property (!idle_ns |=> $stable(req_bank_r));

  // req_row_r update
  assert property (idle_ns |=> req_row_r == $past(row));
  assert property (!idle_ns |=> $stable(req_row_r));

  // req_priority_r update
  assert property (idle_ns |=> req_priority_r == $past(hi_priority));
  assert property (!idle_ns |=> $stable(req_priority_r));

  //============================
  // Hit/busy and maintenance
  //============================

  // rb_hit_busy_ns combinational meaning
  assert property (1'b1 |-> (rb_hit_busy_ns ==
                  (((req_rank_r == (periodic_rd_insert ? periodic_rd_rank_r : rank)) &&
                     (req_bank_r == bank)) && ~idle_ns))));

  // rb_hit_busy_r registered exactly next cycle
  assert property (((req_rank_r == (periodic_rd_insert ? periodic_rd_rank_r : rank)) &&
                     (req_bank_r == bank) && ~idle_ns) |=> rb_hit_busy_r);
  assert property (!((req_rank_r == (periodic_rd_insert ? periodic_rd_rank_r : rank)) &&
                      (req_bank_r == bank) && ~idle_ns) |=> !rb_hit_busy_r);

  // row_hit_r registered next cycle from (req_row_r == row)
  assert property ((req_row_r == row) |=> row_hit_r);
  assert property (!(req_row_r == row) |=> !row_hit_r);

  // maint_hit combinational
  assert property (1'b1 |-> (maint_hit == ((req_rank_r == maint_rank_r) || maint_zq_r || maint_sre_r)));

  //============================
  // Column address composition
  //============================

  // Bit 10: auto-precharge unless half-RMW
  if (ROW_WIDTH > 10) begin
    assert property (1'b1 |-> (col_addr[10] == (auto_pre_r && ~rd_half_rmw)));
  end

  // Bit 11: comes from captured column bit 10 (if available), else 0
  if (ROW_WIDTH > 11) begin
    if (COL_WIDTH > 10)
      assert property (1'b1 |-> (col_addr[11] == f_col_q[10]));
    else
      assert property (1'b1 |-> (col_addr[11] == 1'b0));
  end

  // Bit 12: size
  if (ROW_WIDTH > 12) begin
    assert property (1'b1 |-> (col_addr[12] == req_size_r));
  end

  // Bit 13: comes from captured column bit 11 (if available), else 0
  if (ROW_WIDTH > 13) begin
    if (COL_WIDTH > 11)
      assert property (1'b1 |-> (col_addr[13] == f_col_q[11]));
    else
      assert property (1'b1 |-> (col_addr[13] == 1'b0));
  end

  // All other bits (excluding 10..13) mirror captured column or zero-extend
  genvar i;
  generate
    for (i = 0; i < ROW_WIDTH; i++) begin : G_COL_MIRROR
      if ((i != 10) && (i != 11) && (i != 12) && (i != 13)) begin
        if (i < COL_WIDTH) begin
          assert property (1'b1 |-> (col_addr[i] == f_col_q[i]));
        end else begin
          assert property (1'b1 |-> (col_addr[i] == 1'b0));
        end
      end
    end
  endgenerate

  //============================
  // Row address composition
  //============================
  // When act_wait_r=1: row_addr == req_row_r; when 0: bit10 forced 0, others match
  if (ROW_WIDTH > 10) begin
    assert property ( act_wait_r |-> (row_addr == req_row_r));
    assert property (!act_wait_r |-> (row_addr[10] == 1'b0
                                   && {row_addr[ROW_WIDTH-1:11], row_addr[9:0]}
                                      == {req_row_r[ROW_WIDTH-1:11], req_row_r[9:0]}));
  end else begin
    assert property (1'b1 |-> (row_addr == req_row_r));
  end

  //============================
  // CAS/RAS and row_cmd_wr
  //============================
  assert property (1'b1 |-> (req_ras == 1'b0));
  assert property (1'b1 |-> (req_cas == 1'b1));
  assert property (1'b1 |-> (row_cmd_wr == act_wait_r));

  //============================
  // Rank busy map
  //============================
  localparam [RANKS-1:0] ONE = {{(RANKS-1){1'b0}},1'b1};
  // If not idle, next cycle marks current req_rank_r; if idle, next cycle clears the map
  assert property (!idle_ns |=> (rank_busy_r == (ONE[RANKS-1:0] << req_rank_r)));
  assert property ( idle_ns |=> (rank_busy_r == '0));

  //============================
  // ECC mode guard (matches DUT intent)
  //============================
  // If ECC is OFF, no non-RD/WR cmds should be issued when not idle
  if (ECC == "OFF") begin
    assert property (1'b1 |-> (idle_ns || ~|{cmd[2],cmd[1]}));
  end

  //============================
  // Coverage
  //============================
  // Periodic insertion path
  cover property (idle_ns && periodic_rd_insert ##1 rd_wr_r && !req_wr_r);

  // Normal WR and RD decode paths when idle
  cover property (idle_ns && !periodic_rd_insert && (cmd[1:0]==2'b11) ##1 (rd_wr_r && req_wr_r));
  cover property (idle_ns && !periodic_rd_insert &&  cmd[0]             ##1 (rd_wr_r && !req_wr_r));
  cover property (idle_ns && !periodic_rd_insert && !cmd[0] && (cmd[1:0]!=2'b11) ##1 (!rd_wr_r && req_wr_r));

  // sending_col clears rd_wr while busy
  cover property (!idle_ns && rd_wr_r && sending_col ##1 !rd_wr_r);

  // maint_hit via each disjunct
  cover property ((req_rank_r == maint_rank_r) && !maint_zq_r && !maint_sre_r && idle_ns);
  cover property (maint_zq_r);
  cover property (maint_sre_r);

  // col_addr autoprecharge on/off
  if (ROW_WIDTH > 10) begin
    cover property (auto_pre_r && !rd_half_rmw && col_addr[10]);
    cover property ((!auto_pre_r || rd_half_rmw) && !col_addr[10]);
  end

  // rank_busy coverage (see multiple ranks over time)
  if (RANKS > 1) begin
    genvar rb;
    for (rb=0; rb<RANKS; rb++) begin : G_RB_COV
      cover property (!idle_ns && (req_rank_r == rb[RANK_WIDTH-1:0]) ##1 (rank_busy_r[rb]));
    end
  end

endmodule

bind mig_7series_v1_9_bank_compare
  mig_7series_v1_9_bank_compare_sva #(
    .BANK_WIDTH(BANK_WIDTH),
    .TCQ(TCQ),
    .BURST_MODE(BURST_MODE),
    .COL_WIDTH(COL_WIDTH),
    .DATA_BUF_ADDR_WIDTH(DATA_BUF_ADDR_WIDTH),
    .ECC(ECC),
    .RANK_WIDTH(RANK_WIDTH),
    .RANKS(RANKS),
    .ROW_WIDTH(ROW_WIDTH)
  ) u_mig_7series_v1_9_bank_compare_sva (.*);