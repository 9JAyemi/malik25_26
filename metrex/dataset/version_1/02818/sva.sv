// SVA checker for fifo_64bit
// Bind this file to the DUT. Focused, high‑quality assertions + key coverage.

module fifo_64bit_sva #(parameter int DW=9, DEPTH=64, AW=$clog2(DEPTH)) (
  input  logic                  clk,
  input  logic                  rst,
  input  logic                  wr_en,
  input  logic                  rd_en,
  input  logic [DW-1:0]         din,
  input  logic [DW-1:0]         dout,
  input  logic                  full,
  input  logic                  empty,
  input  logic [AW-1:0]         wr_ptr,
  input  logic [AW-1:0]         rd_ptr,
  input  logic [AW-1:0]         count,
  input  logic [AW-1:0]         next_wr_ptr,
  input  logic [AW-1:0]         next_rd_ptr,
  input  logic [AW-1:0]         next_count
);

  // Static design sanity: count must hold 0..DEPTH (inclusive) -> >= clog2(DEPTH+1)
  // This will FAIL for the provided RTL (count is 6b, needs 7b for DEPTH=64).
  initial begin
    assert ($bits(count) >= $clog2(DEPTH+1))
      else $error("fifo_64bit: 'count' width too small: bits=%0d need >= %0d",
                  $bits(count), $clog2(DEPTH+1));
  end

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset behavior (checked explicitly)
  property p_reset_state;
    @(posedge clk) rst |=> (wr_ptr==0 && rd_ptr==0 && count==0 && empty && !full);
  endproperty
  assert property(p_reset_state);

  // Basic invariants
  assert property (!(full && empty));                // flags mutually exclusive
  assert property (empty == (count==0));             // empty flag consistency
  assert property ((count==DEPTH) |-> full);         // when truly full, flag must be 1
  assert property (full |-> (count==DEPTH));         // full only when truly full

  // Pointer bounds and extreme relationships
  assert property (wr_ptr < DEPTH);
  assert property (rd_ptr < DEPTH);
  assert property ((count==0)     |-> (wr_ptr==rd_ptr));
  assert property ((count==DEPTH) |-> (wr_ptr==rd_ptr));

  // No-ops when illegal ops requested
  assert property (wr_en && full  |=> (wr_ptr==$past(wr_ptr) && count==$past(count)));
  assert property (rd_en && empty |=> (rd_ptr==$past(rd_ptr) && count==$past(count)));

  // Pointer updates and wrap
  assert property (wr_en && !full |=> wr_ptr == $past(next_wr_ptr));
  assert property (rd_en && !empty|=> rd_ptr == $past(next_rd_ptr));

  // Count update protocol (SPEC-compliant)
  // write only
  assert property (wr_en && !full && !(rd_en && !empty)
                   |=> count == $past(count)+1);
  // read only
  assert property (rd_en && !empty && !(wr_en && !full)
                   |=> count == $past(count)-1);
  // simultaneous read & write (both legal): count holds
  assert property (wr_en && rd_en && !full && !empty
                   |=> (count == $past(count) &&
                        wr_ptr == $past(next_wr_ptr) &&
                        rd_ptr == $past(next_rd_ptr)));

  // Combinational next_count correctness (SPEC-compliant encoding)
  assert property (wr_en && !full && !rd_en |-> next_count == (count + 1));
  assert property (rd_en && !empty && !wr_en |-> next_count == (count - 1));
  assert property (wr_en && rd_en && !full && !empty |-> next_count == count);
  assert property ((!wr_en || full) && (!rd_en || empty) |-> next_count == count);

  // Data ordering/scoreboard (concise, cycle-accurate)
  bit [DW-1:0] q[$];
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      q.delete();
    end else begin
      bit wr_fire = wr_en && (q.size() < DEPTH);
      bit rd_fire = rd_en && (q.size() > 0);

      if (wr_fire) q.push_back(din);

      if (rd_fire) begin
        bit [DW-1:0] exp = q.pop_front();
        assert (dout == exp)
          else $error("fifo_64bit data mismatch: exp=%0h got=%0h", exp, dout);
      end

      // DUT count must match model occupancy (integer compare)
      assert ($unsigned(count) == q.size())
        else $error("fifo_64bit count mismatch: dut=%0d ref=%0d", $unsigned(count), q.size());
    end
  end

  // Minimal yet meaningful coverage
  // Reach full (64 valid writes, no reads)
  sequence wr_noread_64;
    (wr_en && !full && !rd_en)[*DEPTH];
  endsequence
  cover property (wr_noread_64 ##1 full);

  // Wrap-around on write pointer
  cover property (wr_en && !full && wr_ptr==DEPTH-1 ##1 wr_ptr==0);

  // Wrap-around on read pointer
  cover property (rd_en && !empty && rd_ptr==DEPTH-1 ##1 rd_ptr==0);

  // Simultaneous read+write when not empty/full
  cover property (wr_en && rd_en && !full && !empty);

  // Drain to empty
  cover property ((rd_en && !empty)[*1:$] ##1 empty);

endmodule

// Bind to the DUT instance(s)
bind fifo_64bit fifo_64bit_sva #(.DW(9), .DEPTH(64), .AW(6)) u_fifo_64bit_sva (
  .clk(clk),
  .rst(rst),
  .wr_en(wr_en),
  .rd_en(rd_en),
  .din(din),
  .dout(dout),
  .full(full),
  .empty(empty),
  .wr_ptr(wr_ptr),
  .rd_ptr(rd_ptr),
  .count(count),
  .next_wr_ptr(next_wr_ptr),
  .next_rd_ptr(next_rd_ptr),
  .next_count(next_count)
);