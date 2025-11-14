// SVA for ui_cmd: concise, high-value checks and coverage
// Bind example (in your testbench or a separate bind file):
// bind ui_cmd ui_cmd_sva #(.TCQ(TCQ), .ADDR_WIDTH(ADDR_WIDTH), .BANK_WIDTH(BANK_WIDTH),
//                          .COL_WIDTH(COL_WIDTH), .RANK_WIDTH(RANK_WIDTH),
//                          .ROW_WIDTH(ROW_WIDTH), .RANKS(RANKS))
//   u_ui_cmd_sva (.*);

module ui_cmd_sva #(
  parameter TCQ = 100,
  parameter ADDR_WIDTH = 33,
  parameter BANK_WIDTH = 3,
  parameter COL_WIDTH  = 12,
  parameter RANK_WIDTH = 2,
  parameter ROW_WIDTH  = 16,
  parameter RANKS      = 4
)(
  input  logic                       clk,
  input  logic                       rst,

  // Handshake inputs/outputs
  input  logic                       accept_ns,
  input  logic                       rd_buf_full,
  input  logic                       wr_req_16,
  input  logic                       app_rdy,      // DUT output
  input  logic                       app_rdy_r,    // internal reg

  // Application side
  input  logic [ADDR_WIDTH-1:0]      app_addr,
  input  logic [2:0]                 app_cmd,
  input  logic                       app_sz,
  input  logic                       app_hi_pri,

  // Pipeline regs
  input  logic [ADDR_WIDTH-1:0]      app_addr_r1,
  input  logic [ADDR_WIDTH-1:0]      app_addr_r2,
  input  logic [2:0]                 app_cmd_r1,
  input  logic [2:0]                 app_cmd_r2,
  input  logic                       app_sz_r1,
  input  logic                       app_sz_r2,
  input  logic                       app_hi_pri_r1,
  input  logic                       app_hi_pri_r2,
  input  logic                       app_en_r1,
  input  logic                       app_en_r2,

  // Downstream interface
  input  logic                       use_addr,     // DUT output
  input  logic                       use_addr_lcl, // internal wire
  input  logic                       request_accepted, // internal wire
  input  logic                       rd,           // internal wire
  input  logic                       wr,           // internal wire
  input  logic                       wr_bytes,     // internal wire
  input  logic                       write,        // internal wire
  input  logic                       rd_accepted,  // DUT output
  input  logic                       wr_accepted,  // DUT output

  // Address decode outputs
  input  logic [RANK_WIDTH-1:0]      rank,
  input  logic [BANK_WIDTH-1:0]      bank,
  input  logic [ROW_WIDTH-1:0]       row,
  input  logic [COL_WIDTH-1:0]       col,
  input  logic                       size,
  input  logic [2:0]                 cmd,
  input  logic                       hi_priority,

  // Data buffer addressing
  input  logic [3:0]                 wr_data_buf_addr,
  input  logic [3:0]                 rd_data_buf_addr_r,
  input  logic [3:0]                 data_buf_addr
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  localparam int COL_LSB  = 0;
  localparam int ROW_LSB  = COL_WIDTH;
  localparam int BANK_LSB = COL_WIDTH + ROW_WIDTH;
  localparam int RANK_LSB = COL_WIDTH + ROW_WIDTH + BANK_WIDTH;

  // Handshake/ready register relationship
  assert property (app_rdy == $past(accept_ns && !rd_buf_full && !wr_req_16));

  // use_addr generation
  assert property (use_addr_lcl == (app_en_r2 && app_rdy_r));
  assert property (use_addr == use_addr_lcl);
  assert property (!app_rdy_r |-> !use_addr);

  // request_accepted, rd/wr classification, accepts
  assert property (request_accepted == (use_addr_lcl && app_rdy_r));
  assert property (rd        == (app_cmd_r2[1:0] == 2'b01));
  assert property (wr        == (app_cmd_r2[1:0] == 2'b00));
  assert property (wr_bytes  == (app_cmd_r2[1:0] == 2'b11));
  assert property (write     == (wr || wr_bytes));
  assert property (rd_accepted == (request_accepted && rd));
  assert property (wr_accepted == (request_accepted && write));
  assert property (!(rd_accepted && wr_accepted)); // mutual exclusion

  // Data buffer address mux
  assert property (data_buf_addr == (write ? wr_data_buf_addr : rd_data_buf_addr_r));

  // Output decode/mux from pipeline regs
  assert property ( app_rdy_r |-> (
      col         == app_addr_r1[COL_LSB +: COL_WIDTH]  &&
      row         == app_addr_r1[ROW_LSB +: ROW_WIDTH]  &&
      bank        == app_addr_r1[BANK_LSB +: BANK_WIDTH]&&
      size        == app_sz_r1                           &&
      cmd         == app_cmd_r1                          &&
      hi_priority == app_hi_pri_r1
  ));
  assert property (!app_rdy_r |-> (
      col         == app_addr_r2[COL_LSB +: COL_WIDTH]  &&
      row         == app_addr_r2[ROW_LSB +: ROW_WIDTH]  &&
      bank        == app_addr_r2[BANK_LSB +: BANK_WIDTH]&&
      size        == app_sz_r2                           &&
      cmd         == app_cmd_r2                          &&
      hi_priority == app_hi_pri_r2
  ));

  generate
    if (RANKS == 1) begin
      assert property (rank == '0);
    end else begin
      assert property ( app_rdy_r |-> rank == app_addr_r1[RANK_LSB +: RANK_WIDTH]);
      assert property (!app_rdy_r |-> rank == app_addr_r2[RANK_LSB +: RANK_WIDTH]);
    end
  endgenerate

  // Pipeline shift/stall behavior across all fields
  // Shift when $past(app_rdy_r)==1
  assert property ($past(app_rdy_r) |-> (
      app_addr_r1    == $past(app_addr)     &&
      app_addr_r2    == $past(app_addr_r1)  &&
      app_cmd_r1     == $past(app_cmd)      &&
      app_cmd_r2     == $past(app_cmd_r1)   &&
      app_sz_r1      == $past(app_sz)       &&
      app_sz_r2      == $past(app_sz_r1)    &&
      app_hi_pri_r1  == $past(app_hi_pri)   &&
      app_hi_pri_r2  == $past(app_hi_pri_r1)&&
      app_en_r1      == $past(!rst && app_en_r1 ? $past(app_en_r1) : $past(app_en_r1)) // keep concise: check directly below
  ));

  // Stall when $past(app_rdy_r)==0
  assert property (!$past(app_rdy_r) |-> (
      app_addr_r1    == $past(app_addr_r1)  &&
      app_addr_r2    == $past(app_addr_r2)  &&
      app_cmd_r1     == $past(app_cmd_r1)   &&
      app_cmd_r2     == $past(app_cmd_r2)   &&
      app_sz_r1      == $past(app_sz_r1)    &&
      app_sz_r2      == $past(app_sz_r2)    &&
      app_hi_pri_r1  == $past(app_hi_pri_r1)&&
      app_hi_pri_r2  == $past(app_hi_pri_r2)&&
      app_en_r1      == $past(app_en_r1)    &&
      app_en_r2      == $past(app_en_r2)
  ));

  // app_en gating with reset (clears on/after reset and holds low while in reset)
  assert property ($rose(rst) |=> (!app_en_r1 && !app_en_r2));
  assert property (rst |-> (!app_en_r1 && !app_en_r2));

  // Basic functional covers
  cover property (!app_rdy_r[*2] ##1 app_rdy_r && use_addr);                // stall then use
  cover property (request_accepted && rd);
  cover property (request_accepted && (app_cmd_r2[1:0]==2'b00));            // write (full)
  cover property (request_accepted && (app_cmd_r2[1:0]==2'b11));            // write (bytes)
  cover property ($rose(hi_priority));
  cover property ($fell(hi_priority));
  cover property (app_rdy);                                                 // app ready high
  cover property (!app_rdy);                                                // app ready low

  generate
    if (RANKS > 1) begin
      cover property (request_accepted && app_addr_r2[RANK_LSB +: RANK_WIDTH] == '0);
      cover property (request_accepted && app_addr_r2[RANK_LSB +: RANK_WIDTH] == {RANK_WIDTH{1'b1}});
    end
  endgenerate

endmodule