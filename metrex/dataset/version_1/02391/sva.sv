// SVA checker for fifo. Bind this to the DUT.
// Note: This builds a golden occupancy model independent of DUT full/empty,
// checks flags, pointer/count updates, ordering, and adds concise coverage.

module fifo_asserts #(
  parameter int DEPTH   = 16,
  parameter int PTR_W   = $clog2(DEPTH),
  parameter int COUNT_W = $clog2(DEPTH+1)
)(
  input  logic                 clk,
  input  logic                 rst,
  input  logic [7:0]           din,
  input  logic                 wr_en,
  input  logic                 rd_en,
  input  logic [7:0]           dout,
  input  logic                 full,
  input  logic                 empty,
  input  logic [PTR_W-1:0]     wr_ptr,
  input  logic [PTR_W-1:0]     rd_ptr,
  input  logic [COUNT_W-1:0]   count
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Golden occupancy model (independent of DUT flags)
  logic [COUNT_W-1:0] m_count;
  logic               mw, mr; // model-allowed write/read

  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      m_count <= '0;
      mw      <= 1'b0;
      mr      <= 1'b0;
    end else begin
      mw <= wr_en && (m_count < DEPTH);
      mr <= rd_en && (m_count > 0);
      m_count <= m_count + (mw ? 1 : 0) - (mr ? 1 : 0);
    end
  end

  // Reset state (checked during reset)
  always_ff @(posedge clk) if (rst) begin
    assert (wr_ptr == '0 && rd_ptr == '0 && count == '0)
      else $error("Reset state wrong: wr_ptr=%0d rd_ptr=%0d count=%0d", wr_ptr, rd_ptr, count);
    assert (empty && !full)
      else $error("Reset flags wrong: empty=%0b full=%0b", empty, full);
  end

  // Flags must reflect golden occupancy
  assert property (full  == (m_count == DEPTH))
    else $error("full flag mismatch vs model: m_count=%0d full=%0b", m_count, full);

  assert property (empty == (m_count == 0))
    else $error("empty flag mismatch vs model: m_count=%0d empty=%0b", m_count, empty);

  // full and empty never both 1
  assert property (!(full && empty)) else $error("full && empty both asserted");

  // Count should update consistent with model-allowed ops
  assert property ( $past(mw) && !$past(mr) |-> count == $past(count) + 1 )
    else $error("count did not increment on write");
  assert property ( $past(mr) && !$past(mw) |-> count == $past(count) - 1 )
    else $error("count did not decrement on read");
  assert property ( ($past(mw) && $past(mr)) || (!$past(mw) && !$past(mr)) |-> count == $past(count) )
    else $error("count changed unexpectedly");

  // Write/read pointer updates per model-allowed ops
  assert property ( $past(mw) |-> wr_ptr == $past(wr_ptr) + 1 )
    else $error("wr_ptr did not advance on write");
  assert property ( !$past(mw) |-> wr_ptr == $past(wr_ptr) )
    else $error("wr_ptr changed without write");

  assert property ( $past(mr) |-> rd_ptr == $past(rd_ptr) + 1 )
    else $error("rd_ptr did not advance on read");
  assert property ( !$past(mr) |-> rd_ptr == $past(rd_ptr) )
    else $error("rd_ptr changed without read");

  // When model says "no read", dout must hold its value (design only updates on read)
  assert property ( !$past(mr) |-> dout == $past(dout) )
    else $error("dout changed without a read");

  // Blocked ops must not change pointers or count (overflow/underflow protection vs model)
  assert property ( (m_count == DEPTH) && $past(wr_en) && !$past(rd_en) |-> wr_ptr == $past(wr_ptr) && count == $past(count) )
    else $error("State changed on write when model-full");
  assert property ( (m_count == 0) && $past(rd_en) && !$past(wr_en) |-> rd_ptr == $past(rd_ptr) && count == $past(count) )
    else $error("State changed on read when model-empty");

  // Internal self-consistency (sanity)
  assert property ( count <= DEPTH )
    else $error("DUT count exceeded DEPTH encoding");
  assert property ( full |-> !empty ) else $error("full implies empty");

  // Data ordering check with a tiny model queue
  byte q[$];
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      q.delete();
    end else begin
      if (mw) q.push_back(din);
      if (mr) begin
        byte exp;
        assert (q.size() > 0) else $error("Model underflow");
        exp = q.pop_front();
        assert (dout === exp) else $error("Data mismatch: got %0h exp %0h", dout, exp);
      end
    end
  end

  // Coverage: reach full; reach empty; simultaneous rd/wr; pointer wrap
  cover property ( m_count == DEPTH );
  cover property ( m_count == 0 );
  cover property ( m_count inside {[1:DEPTH-1]} && mw && mr );
  cover property ( $past(mw) && $past(wr_ptr) == (DEPTH-1) && wr_ptr == '0 ); // wr wrap
  cover property ( $past(mr) && $past(rd_ptr) == (DEPTH-1) && rd_ptr == '0 ); // rd wrap

endmodule

// Example bind (place in a package or a separate file compiled after DUT):
// bind fifo fifo_asserts #(.DEPTH(DEPTH)) fifo_sva (
//   .clk(clk), .rst(rst),
//   .din(din), .wr_en(wr_en), .rd_en(rd_en),
//   .dout(dout), .full(full), .empty(empty),
//   .wr_ptr(wr_ptr), .rd_ptr(rd_ptr), .count(count)
// );