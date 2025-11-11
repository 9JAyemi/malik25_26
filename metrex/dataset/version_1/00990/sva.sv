// SVA checker for fifo_buffer
module fifo_buffer_sva #(parameter int DEPTH=16) (
  input logic               clk,
  input logic               rst,
  input logic               wr_en,
  input logic               rd_en,
  input logic [31:0]        data_in,
  input logic [31:0]        data_out,
  input logic [5:0]         head,
  input logic [5:0]         tail,
  input logic [5:0]         count,
  input logic [31:0]        buffer [0:DEPTH-1]
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Derived controls
  wire full    = (count == DEPTH);
  wire empty   = (count == 0);
  wire wr_only = wr_en && !rd_en;
  wire rd_only = rd_en && !wr_en;
  wire both    = wr_en && rd_en;

  // Reset state
  a_reset:        assert property (rst |=> head==0 && tail==0 && count==0);

  // Range/bounds
  a_cnt_bounds:   assert property (count <= DEPTH);
  a_head_bounds:  assert property (head  <  DEPTH);
  a_tail_bounds:  assert property (tail  <  DEPTH);

  // Next-state for counters/pointers
  a_count_next:   assert property (1 |=> count == $past(count)
                                   + ($past(wr_only && !full)  ? 6'd1 : 6'd0)
                                   - ($past(rd_only && !empty) ? 6'd1 : 6'd0));
  a_head_next:    assert property (1 |=> head  == $past(head)
                                   + ($past(wr_only && !full)  ? 6'd1 : 6'd0));
  a_tail_next:    assert property (1 |=> tail  == $past(tail)
                                   + ($past(rd_only && !empty) ? 6'd1 : 6'd0));

  // No-ops on disallowed ops and simultaneous wr/rd
  a_overflow_noop:  assert property (wr_only && full  |=> head==$past(head) && tail==$past(tail) && count==$past(count) && $stable(data_out));
  a_underflow_noop: assert property (rd_only && empty |=> head==$past(head) && tail==$past(tail) && count==$past(count) && $stable(data_out));
  a_both_noop:      assert property (both             |=> head==$past(head) && tail==$past(tail) && count==$past(count) && $stable(data_out));

  // Data movement correctness
  a_write_store:  assert property (wr_only && !full |=> buffer[$past(head)] == $past(data_in));
  a_read_data:    assert property (rd_only && !empty |=> data_out == $past(buffer[$past(tail)]));

  // data_out only changes on successful read
  a_data_stable:  assert property (!(rd_only && !empty) |=> $stable(data_out));

  // Basic functional coverage
  c_write:        cover property (wr_only && !full);
  c_read:         cover property (rd_only && !empty);
  c_full:         cover property (count == DEPTH);
  c_empty:        cover property (count == 0);
  c_wr_then_rd:   cover property ((wr_only && !full) ##[1:$] (rd_only && !empty));
  c_both:         cover property (both);
  c_overflow:     cover property (wr_only && full);
  c_underflow:    cover property (rd_only && empty);
endmodule

// Bind into DUT
bind fifo_buffer fifo_buffer_sva #(.DEPTH(DEPTH)) fifo_buffer_sva_i (
  .clk      (clk),
  .rst      (rst),
  .wr_en    (wr_en),
  .rd_en    (rd_en),
  .data_in  (data_in),
  .data_out (data_out),
  .head     (head),
  .tail     (tail),
  .count    (count),
  .buffer   (buffer)
);