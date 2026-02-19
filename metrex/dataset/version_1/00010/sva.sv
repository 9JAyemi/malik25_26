module fifo_buffer_sva #(
  parameter int DEPTH = 64,
  parameter int WIDTH = 8
)(
  // DUT ports
  input logic clk,
  input logic fifo_rd,
  input logic rst_n,
  input logic fifo_EF,
  input logic [WIDTH-1:0] fifo_rdata,
  input logic rfifo_full,
  input logic [5:0] rfifo_used,

  // DUT internals (bind these via hierarchical refs)
  input logic [6:0] write_ptr,
  input logic [6:0] read_ptr,
  input logic [6:0] used_entries
);

  //////////////////////////////////////////////////////////////////////////////
  // Analysis summary (from RTL):
  // - Clock: clk (posedge)
  // - Reset: rst_n (active-low, asynchronous in RTL), assertions are clocked
  // - Logic type: Sequential (two always @(posedge clk or negedge rst_n) blocks)
  // - Key behaviors present in RTL:
  //   * used_entries increments by 1 every cycle when not full; never decrements.
  //   * fifo_full iff used_entries == DEPTH; fifo_empty iff used_entries == 0.
  //   * write_ptr increments by 1 every cycle when not full; otherwise holds.
  //   * On read when not empty: fifo_rdata <= fifo_mem[read_ptr], read_ptr++,
  //     rfifo_used <= used_entries - 1. Otherwise these hold their previous values.
  //   * Reset drives pointers, counters, and visible outputs low (empty=1, full=0).
  //////////////////////////////////////////////////////////////////////////////

  // Derived internal status (reconstructed from DUT equations)
  wire fifo_empty_int = (used_entries == 0);
  wire fifo_full_int  = (used_entries == DEPTH);

  localparam int DEPTHM1 = DEPTH - 1;

  ///// Reset behavior /////
  // When reset is asserted, pointers/counters are cleared, EF=1, FULL=0, outputs cleared.
  check_reset_defaults: assert property (
    @(posedge clk)
      (!rst_n) |-> (read_ptr == 7'd0) && (write_ptr == 7'd0) && (used_entries == 7'd0) &&
                  (fifo_rdata == {WIDTH{1'b0}}) && (rfifo_used == 6'd0) &&
                  (fifo_EF == 1'b1) && (rfifo_full == 1'b0)
  );

  ///// Status outputs must reflect internal counts /////
  // fifo_EF equals (used_entries == 0)
  check_empty_output_matches_count: assert property (
    @(posedge clk) disable iff (!rst_n)
      fifo_EF == (used_entries == 7'd0)
  );

  // rfifo_full equals (used_entries == DEPTH)
  check_full_output_matches_count: assert property (
    @(posedge clk) disable iff (!rst_n)
      rfifo_full == (used_entries == DEPTH[6:0])
  );

  // Empty and full cannot be asserted simultaneously.
  check_empty_full_mutex: assert property (
    @(posedge clk) disable iff (!rst_n)
      !(fifo_EF && rfifo_full)
  );

  ///// used_entries counter behavior /////
  // used_entries never decreases (it either increments by 1 or holds).
  check_used_entries_monotonic: assert property (
    @(posedge clk) disable iff (!rst_n)
      used_entries >= $past(used_entries)
  );

  // When not full in the previous cycle, used_entries increments by 1.
  check_used_entries_inc_when_not_full: assert property (
    @(posedge clk) disable iff (!rst_n)
      !$past(fifo_full_int) |-> (used_entries == $past(used_entries) + 7'd1)
  );

  // When full in the previous cycle, used_entries holds its value.
  check_used_entries_hold_when_full: assert property (
    @(posedge clk) disable iff (!rst_n)
      $past(fifo_full_int) |-> (used_entries == $past(used_entries))
  );

  // Once used_entries reaches DEPTH, it stays at DEPTH (saturates).
  check_used_entries_saturates_at_depth: assert property (
    @(posedge clk) disable iff (!rst_n)
      (used_entries == DEPTH[6:0]) |=> (used_entries == DEPTH[6:0])
  );

  // used_entries is always within [0, DEPTH]
  check_used_entries_range: assert property (
    @(posedge clk) disable iff (!rst_n)
      used_entries <= DEPTH[6:0]
  );

  ///// write_ptr behavior /////
  // When not full in the previous cycle, write_ptr increments by 1.
  check_write_ptr_inc_when_not_full: assert property (
    @(posedge clk) disable iff (!rst_n)
      !$past(fifo_full_int) |-> (write_ptr == $past(write_ptr) + 7'd1)
  );

  // When full in the previous cycle, write_ptr holds its value.
  check_write_ptr_hold_when_full: assert property (
    @(posedge clk) disable iff (!rst_n)
      $past(fifo_full_int) |-> (write_ptr == $past(write_ptr))
  );

  // If write_ptr changes, it must be due to not-full in the previous cycle and by +1.
  check_write_ptr_changes_only_when_not_full: assert property (
    @(posedge clk) disable iff (!rst_n)
      (write_ptr != $past(write_ptr)) |-> (!$past(fifo_full_int) && (write_ptr == $past(write_ptr) + 7'd1))
  );

  ///// read side behavior /////
  // On a valid read (fifo_rd && !empty) in the previous cycle, read_ptr increments by 1.
  check_read_ptr_inc_on_valid_read: assert property (
    @(posedge clk) disable iff (!rst_n)
      $past(fifo_rd && !fifo_empty_int) |-> (read_ptr == $past(read_ptr) + 7'd1)
  );

  // If there was no valid read in the previous cycle, read_ptr holds.
  check_read_ptr_hold_without_valid_read: assert property (
    @(posedge clk) disable iff (!rst_n)
      !$past(fifo_rd && !fifo_empty_int) |-> (read_ptr == $past(read_ptr))
  );

  // If read_ptr changes, it must be due to a valid read in the previous cycle and by +1.
  check_read_ptr_changes_only_on_valid_read: assert property (
    @(posedge clk) disable iff (!rst_n)
      (read_ptr != $past(read_ptr)) |-> ($past(fifo_rd && !fifo_empty_int) && (read_ptr == $past(read_ptr) + 7'd1))
  );

  // On a valid read in the previous cycle, rfifo_used updates to used_entries - 1 (lower 6 bits).
  check_rfifo_used_updates_on_valid_read: assert property (
    @(posedge clk) disable iff (!rst_n)
      $past(fifo_rd && !fifo_empty_int) |-> ({1'b0, rfifo_used} == ($past(used_entries) - 7'd1))
  );

  // If there was no valid read in the previous cycle, rfifo_used holds.
  check_rfifo_used_hold_without_valid_read: assert property (
    @(posedge clk) disable iff (!rst_n)
      !$past(fifo_rd && !fifo_empty_int) |-> (rfifo_used == $past(rfifo_used))
  );

  // If there was no valid read in the previous cycle, fifo_rdata holds.
  check_rdata_hold_without_valid_read: assert property (
    @(posedge clk) disable iff (!rst_n)
      !$past(fifo_rd && !fifo_empty_int) |-> (fifo_rdata == $past(fifo_rdata))
  );

  // If a read is requested while empty, no read-side observable state changes.
  check_no_update_on_read_when_empty: assert property (
    @(posedge clk) disable iff (!rst_n)
      $past(fifo_rd && fifo_empty_int) |-> (read_ptr == $past(read_ptr)) &&
                                         (rfifo_used == $past(rfifo_used)) &&
                                         (fifo_rdata == $past(fifo_rdata))
  );

  ///// Derived status monotonicity (from used_entries monotonicity) /////
  // rfifo_full cannot fall after reset deassertion (once 1, stays 1).
  check_full_not_falling: assert property (
    @(posedge clk) disable iff (!rst_n)
      !$fell(rfifo_full)
  );

  // fifo_EF cannot rise after reset deassertion (once 0, stays 0).
  check_empty_not_rising: assert property (
    @(posedge clk) disable iff (!rst_n)
      !$rose(fifo_EF)
  );

  // When used_entries moves from DEPTH-1 to DEPTH, rfifo_full rises in the next cycle.
  check_full_rises_when_reaching_depth: assert property (
    @(posedge clk) disable iff (!rst_n)
      ($past(used_entries) == DEPTHM1[6:0] && !$past(fifo_full_int)) |-> rfifo_full
  );

endmodule