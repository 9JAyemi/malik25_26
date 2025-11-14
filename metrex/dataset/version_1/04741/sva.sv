// SVA checker for fifo_buffer. Bind this to the DUT.
// Focuses on safety, control/flag correctness, priority, data ordering, and coverage.

module fifo_buffer_sva #(
  parameter int WIDTH = 8,
  parameter int DEPTH = 64,
  parameter int MAX   = DEPTH-1
)(
  input  logic              clk,
  input  logic              rst_n,
  input  logic              fifo_clear,
  input  logic              fifo_rd,
  input  logic              wr_rfifo,
  input  logic [WIDTH-1:0]  t_dat,
  input  logic              fifo_EF,
  input  logic              rfifo_full,
  input  logic [WIDTH-1:0]  fifo_rdata,
  input  logic [5:0]        rfifo_used
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Flag correctness
  assert property (rfifo_full == (rfifo_used == MAX))
    else $error("rfifo_full mismatch");
  assert property (fifo_EF    == (rfifo_used == 0))
    else $error("fifo_EF mismatch");

  // Range
  assert property (rfifo_used <= MAX)
    else $error("rfifo_used out of range");

  // Reset/clear behavior (reset is synchronous; do not disable on reset)
  property p_reset_sync; !rst_n |=> (rfifo_used == 0 && fifo_EF); endproperty
  assert property (disable iff (1'b0) p_reset_sync)
    else $error("Reset did not clear FIFO");
  assert property (fifo_clear |=> (rfifo_used == 0 && fifo_EF))
    else $error("fifo_clear did not clear FIFO");

  // Write effect
  assert property ((wr_rfifo && (rfifo_used != MAX)) |=> rfifo_used == $past(rfifo_used) + 1)
    else $error("Write did not increment used");
  // Write blocked when full
  assert property ((wr_rfifo && (rfifo_used == MAX)) |=> rfifo_used == $past(rfifo_used))
    else $error("Used changed on write when full");

  // Read effect with write priority (write wins when both possible)
  function automatic logic read_takes_effect(logic wr, logic rd, logic [5:0] used);
    return rd && (used != 0) && !(wr && (used != MAX));
  endfunction

  assert property (read_takes_effect(wr_rfifo, fifo_rd, rfifo_used) |=> rfifo_used == $past(rfifo_used) - 1)
    else $error("Read did not decrement used");

  // Read blocked when empty or when write takes priority
  assert property ((fifo_rd && ((rfifo_used == 0) || (wr_rfifo && (rfifo_used != MAX)))) |=> rfifo_used == $past(rfifo_used))
    else $error("Used changed on blocked read");

  // Simultaneous r/w when both possible => write wins
  assert property ((wr_rfifo && fifo_rd && (rfifo_used != MAX) && (rfifo_used != 0)) |=> rfifo_used == $past(rfifo_used) + 1)
    else $error("Write did not take priority over read");

  // Knownness
  assert property (!$isunknown({rfifo_used, rfifo_full, fifo_EF}))
    else $error("Unknown on flags/used");
  assert property (read_takes_effect(wr_rfifo, fifo_rd, rfifo_used) |-> !$isunknown(fifo_rdata))
    else $error("Unknown fifo_rdata on read");

  // Lightweight scoreboard (golden queue) for ordering/data correctness and count check
  logic [WIDTH-1:0] q[$];
  logic do_write_c, do_read_c;

  always_comb begin
    do_write_c = wr_rfifo && (q.size() != DEPTH);
    do_read_c  = fifo_rd  && (q.size() != 0) && !do_write_c; // write has priority
  end

  always_ff @(posedge clk) begin
    if (!rst_n || fifo_clear) begin
      q.delete();
    end else begin
      if (do_write_c) q.push_back(t_dat);
      if (do_read_c) begin
        assert (fifo_rdata == q[0])
          else $error("Data mismatch: exp=%0h got=%0h depth=%0d", q[0], fifo_rdata, q.size());
        q.pop_front();
      end
    end
    assert (q.size() == rfifo_used)
      else $error("Used count mismatch: model=%0d dut=%0d", q.size(), rfifo_used);
  end

  // Coverage
  cover property ($rose(rst_n));
  cover property (fifo_clear);
  cover property (wr_rfifo && (rfifo_used == MAX)); // attempt write on full
  cover property (fifo_rd && (rfifo_used == 0));    // attempt read on empty
  cover property (wr_rfifo && fifo_rd && (rfifo_used inside {[1:MAX-1]})); // concurrent r/w
  cover property (rfifo_used==0 ##1 wr_rfifo[*2] ##1 rfifo_used==2 ##1 fifo_rd[*2] ##1 rfifo_used==0); // basic fill/drain
  cover property (rfifo_used==MAX ##1 fifo_rd[*MAX] ##1 rfifo_used==0); // drain from full

endmodule

bind fifo_buffer fifo_buffer_sva #(.WIDTH(8), .DEPTH(64)) i_fifo_buffer_sva (.*);