// SVA for fifo_24in_24out_12kb_updn_cntr
// Focused, concise checks for pointer movement, count arithmetic, memory R/W,
// and 1-cycle output pipelines; includes key covers.

checker fifo_24in_24out_12kb_updn_cntr_sva (
  input  logic               clk,
  // DUT ports
  input  logic               rd_en,
  input  logic               valid_fwft,
  input  logic [23:0]        Q,
  input  logic [23:0]        data_out,
  input  logic               data_count_out,
  input  logic               rd_en_out,
  input  logic               valid_fwft_out,
  input  logic [23:0]        Q_out,
  // DUT internals
  input  logic [8:0]         rd_ptr,
  input  logic [8:0]         wr_ptr,
  input  logic [8:0]         next_rd_ptr,
  input  logic [8:0]         next_wr_ptr,
  input  logic [9:0]         data_count,
  input  logic [9:0]         data_count_internal,
  input  logic [9:0]         next_data_count,
  input  logic               rd_en_internal,
  input  logic               valid_fwft_internal,
  input  logic [23:0]        data_out_internal,
  input  var   logic [23:0]  mem[]   // open array binds to mem[0:511]
);
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  localparam int unsigned MEM_SIZE = 512;
  localparam int unsigned MAX_PTR  = MEM_SIZE-1;

  function automatic logic [8:0] inc_ptr(input logic [8:0] p);
    return (p == MAX_PTR) ? 9'd0 : p + 9'd1;
  endfunction

  // Sanity: no X on key controls/state
  assert property (!$isunknown({rd_en, rd_en_internal, rd_ptr, wr_ptr, data_count, data_count_internal})));

  // Pointer updates (rd_ptr depends on rd_en this cycle; wr_ptr depends on rd_en last cycle)
  assert property (rd_en |=> rd_ptr == inc_ptr($past(rd_ptr)));
  assert property (!rd_en |=> rd_ptr == $past(rd_ptr)));
  assert property ($past(rd_en) |=> wr_ptr == inc_ptr($past(wr_ptr)));
  assert property (!$past(rd_en) |=> wr_ptr == $past(wr_ptr)));

  // Pointer updates match DUT next_* wires
  assert property (rd_en |=> rd_ptr == $past(next_rd_ptr));
  assert property ($past(rd_en) |=> wr_ptr == $past(next_wr_ptr));

  // Count arithmetic and mirroring
  assert property (1 |=> data_count == $past(next_data_count));
  assert property (data_count_internal == data_count);

  // 1-cycle output pipelines
  assert property (Q_out == $past(Q)));
  assert property (rd_en_out == $past(rd_en)));
  assert property (valid_fwft_out == $past(valid_fwft)));
  assert property (rd_en_internal == $past(rd_en)));
  assert property (valid_fwft_internal == $past(valid_fwft)));
  assert property (data_out == $past(data_out_internal)));
  assert property (data_count_out == $past(data_count_internal[8]))); // bit [ADDR_WIDTH-1] = bit 8

  // Read datapath: data_out equals prior-cycle mem at prior rd_ptr
  assert property (data_out == $past(mem[rd_ptr])));

  // Memory write behavior:
  // Write occurs only when both last and current rd_en are 0; otherwise location holds
  assert property ((!$past(rd_en) && !rd_en) |=> mem[$past(wr_ptr)] == $past(Q)));
  assert property (($past(rd_en) || rd_en)   |=> mem[$past(wr_ptr)] == $past(mem[$past(wr_ptr)])));

  // Wrap-around covers
  cover property (rd_ptr == MAX_PTR && rd_en ##1 rd_ptr == 9'd0);
  cover property (wr_ptr == MAX_PTR && $past(rd_en) ##1 wr_ptr == 9'd0);

  // Exercise write and no-write paths
  cover property ((!$past(rd_en) && !rd_en) ##1 mem[$past(wr_ptr)] == $past(Q));
  cover property (($past(rd_en) || rd_en)));

  // Exercise output pipelines
  cover property ($changed(Q) ##1 Q_out == $past(Q));
  cover property ($changed(valid_fwft) ##1 valid_fwft_out == $past(valid_fwft));
  cover property ($changed(rd_en) ##1 rd_en_out == $past(rd_en));
endchecker

bind fifo_24in_24out_12kb_updn_cntr fifo_24in_24out_12kb_updn_cntr_sva chk (
  .clk                (clk),
  .rd_en              (rd_en),
  .valid_fwft         (valid_fwft),
  .Q                  (Q),
  .data_out           (data_out),
  .data_count_out     (data_count_out),
  .rd_en_out          (rd_en_out),
  .valid_fwft_out     (valid_fwft_out),
  .Q_out              (Q_out),
  .rd_ptr             (rd_ptr),
  .wr_ptr             (wr_ptr),
  .next_rd_ptr        (next_rd_ptr),
  .next_wr_ptr        (next_wr_ptr),
  .data_count         (data_count),
  .data_count_internal(data_count_internal),
  .next_data_count    (next_data_count),
  .rd_en_internal     (rd_en_internal),
  .valid_fwft_internal(valid_fwft_internal),
  .data_out_internal  (data_out_internal),
  .mem                (mem)
);