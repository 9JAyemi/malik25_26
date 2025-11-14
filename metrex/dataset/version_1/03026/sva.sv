// SVA checker for fifo. Bind this to the DUT.
// Focuses on safety (no overflow/underflow), flag correctness, pointer updates,
// data ordering, and basic coverage.

module fifo_sva #(
  parameter int DEPTH   = 32,
  parameter int ADDR_W  = $clog2(DEPTH)
)(
  input  logic         clk,
  input  logic         reset,

  // DUT ports
  input  logic  [7:0]  io_dataIn,
  input  logic  [7:0]  io_dataOut,
  input  logic         io_read,
  input  logic         io_write,
  input  logic         io_full,
  input  logic         io_empty,

  // DUT internals
  input  logic [ADDR_W-1:0] head,
  input  logic [ADDR_W-1:0] tail,
  input  logic [ADDR_W-1:0] next_head,
  input  logic [ADDR_W-1:0] next_tail,
  input  logic              full,
  input  logic              empty
);

  default clocking cb @(posedge clk); endclocking

  // Basic consistency mapping between internal and outputs
  assert property (cb disable iff (reset) io_full  == full);
  assert property (cb disable iff (reset) io_empty == empty);
  assert property (cb disable iff (reset) !(io_full && io_empty));

  // next_* must reflect previous cycle head/tail + reqs (due to <= semantics)
  assert property (cb disable iff (reset) next_head == $past(head) + $past(io_write));
  assert property (cb disable iff (reset) next_tail == $past(tail) + $past(io_read));

  // Golden reference model (independent of DUT flags)
  logic [ADDR_W:0] occ_ref; // 0..DEPTH
  logic wr_en_ref, rd_en_ref;
  byte  q[$];

  always_ff @(posedge clk) begin
    if (reset) begin
      occ_ref   <= '0;
      q.delete();
    end else begin
      wr_en_ref = (io_write && (occ_ref < DEPTH));
      rd_en_ref = (io_read  && (occ_ref > 0));

      // Push before checking output
      if (wr_en_ref)
        q.push_back(io_dataIn);

      // Output check: when not empty by spec, front of queue must be visible
      if (occ_ref == 0) begin
        assert (io_dataOut == 8'h00);
      end else begin
        if (q.size() > 0) assert (io_dataOut === q[0]);
      end

      // Pop on read
      if (rd_en_ref) begin
        assert (q.size() > 0);
        if (q.size() > 0) void'(q.pop_front());
      end

      // Update occupancy
      occ_ref <= occ_ref + (wr_en_ref ? 1 : 0) - (rd_en_ref ? 1 : 0);

      // Occ bounds
      assert (occ_ref <= DEPTH);
    end
  end

  // Flags must match golden occupancy
  assert property (cb reset |-> io_empty && !io_full);
  assert property (cb disable iff (reset) (occ_ref == 0)      |->  io_empty && !io_full);
  assert property (cb disable iff (reset) (occ_ref == DEPTH)  |->  io_full  && !io_empty);
  assert property (cb disable iff (reset) (occ_ref > 0 && occ_ref < DEPTH) |-> !io_full && !io_empty);

  // Pointers update per accepted ops (golden acceptance)
  function automatic logic [ADDR_W-1:0] inc_wrap(input logic [ADDR_W-1:0] v);
    return (v == DEPTH-1) ? '0 : v + 1'b1;
  endfunction

  // Head: increments on write-accept, holds otherwise
  assert property (cb disable iff (reset)
                   wr_en_ref |-> head == inc_wrap($past(head)));
  assert property (cb disable iff (reset)
                   !wr_en_ref |-> head == $past(head));

  // Tail: increments on read-accept, holds otherwise
  assert property (cb disable iff (reset)
                   rd_en_ref |-> tail == inc_wrap($past(tail)));
  assert property (cb disable iff (reset)
                   !rd_en_ref |-> tail == $past(tail));

  // Illegal attempts must not move pointers
  assert property (cb disable iff (reset)
                   (io_write && (occ_ref == DEPTH)) |-> head == $past(head));
  assert property (cb disable iff (reset)
                   (io_read  && (occ_ref == 0))     |-> tail == $past(tail));

  // Pointer/occupancy relation
  assert property (cb disable iff (reset)
                   (head == tail) |-> (occ_ref == 0 || occ_ref == DEPTH));

  // DataOut must be known (no X) whenever spec says non-empty
  assert property (cb disable iff (reset) (occ_ref > 0) |-> !$isunknown(io_dataOut));

  // Coverage: reset -> empty; fill to full; drain to empty; simultaneous R/W; wrap-arounds; overflow/underflow attempts
  cover property (cb reset ##1 !reset && io_empty && !io_full);
  cover property (cb disable iff (reset) $rose(io_full));
  cover property (cb disable iff (reset) $rose(io_empty));
  cover property (cb disable iff (reset) (!io_full && !io_empty && io_write && io_read));
  cover property (cb disable iff (reset) ($past(head)==DEPTH-1 && wr_en_ref ##1 head==0));
  cover property (cb disable iff (reset) ($past(tail)==DEPTH-1 && rd_en_ref ##1 tail==0));
  cover property (cb disable iff (reset) (io_write && (occ_ref == DEPTH))); // overflow attempt
  cover property (cb disable iff (reset) (io_read  && (occ_ref == 0)));     // underflow attempt

endmodule

// Bind to DUT type
bind fifo fifo_sva #(.DEPTH(32)) u_fifo_sva (
  .clk(clk),
  .reset(reset),
  .io_dataIn(io_dataIn),
  .io_dataOut(io_dataOut),
  .io_read(io_read),
  .io_write(io_write),
  .io_full(io_full),
  .io_empty(io_empty),
  .head(head),
  .tail(tail),
  .next_head(next_head),
  .next_tail(next_tail),
  .full(full),
  .empty(empty)
);