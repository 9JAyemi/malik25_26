// SVA checker for fifo2. Bind this to the DUT.
// Focuses on reset, flags, pointer movement, overflow/underflow protection,
// data ordering, and corner-case coverage.

module fifo2_sva #(parameter SIZE=2, parameter DEPTH_LOG2=1)
(
  input logic                   clk,
  input logic                   reset,
  input logic                   write,
  input logic                   read,
  input logic [SIZE-1:0]        item_in,
  input logic [SIZE-1:0]        item_out,
  input logic                   full,
  input logic                   empty
);

  localparam int DEPTH = 2**DEPTH_LOG2;

  // Default clock/reset for concurrent properties
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // --------------------
  // Basic reset checks
  // --------------------
  // Asynchronous reset state
  assert property (@(posedge reset)
    (read_ptr == '0 && write_ptr == '0 && empty && !full)
  ) else $error("Reset state incorrect");

  // --------------------
  // Flag consistency and exclusivity
  // --------------------
  // Empty/full never both 1
  assert property ( !(full && empty) )
    else $error("full && empty both asserted");

  // When empty or full, pointers must be equal (this FIFO disambiguates equal pointers via flags)
  assert property ( empty |-> (read_ptr == write_ptr) )
    else $error("empty asserted but pointers not equal");

  assert property ( full  |-> (read_ptr == write_ptr) )
    else $error("full asserted but pointers not equal");

  // If pointers equal, exactly one of empty/full must be 1
  assert property ( (read_ptr == write_ptr) |-> (full ^ empty) )
    else $error("pointers equal but flags inconsistent");

  // If pointers not equal, both empty and full must be 0
  assert property ( (read_ptr != write_ptr) |-> (!empty && !full) )
    else $error("pointers not equal but flags not both deasserted");

  // --------------------
  // Gating and no-ops at boundaries
  // --------------------
  // No write-only action when full
  assert property ( (full && write && !read) |=> (write_ptr == $past(write_ptr) &&
                                                 read_ptr  == $past(read_ptr)  &&
                                                 full      == $past(full)      &&
                                                 empty     == $past(empty)) )
    else $error("Write attempted while full changed state");

  // No read-only action when empty
  assert property ( (empty && read && !write) |=> (write_ptr == $past(write_ptr) &&
                                                  read_ptr  == $past(read_ptr)  &&
                                                  full      == $past(full)      &&
                                                  empty     == $past(empty)) )
    else $error("Read attempted while empty changed state");

  // --------------------
  // Pointer update semantics and flag updates
  // --------------------
  // Both read and write (only allowed when !empty && !full): both pointers advance, flags hold
  assert property ( (read && !empty) && (write && !full) |=> (read_ptr  == $past(read_ptr + 1) &&
                                                              write_ptr == $past(write_ptr + 1) &&
                                                              full      == $past(full) &&
                                                              empty     == $past(empty)) )
    else $error("Simultaneous read/write pointer/flag update error");

  // Read only: read_ptr advances, write_ptr holds, full cleared
  assert property ( (read && !empty) && !(write && !full) |=> (read_ptr  == $past(read_ptr + 1) &&
                                                               write_ptr == $past(write_ptr)     &&
                                                               full      == 1'b0                 &&
                                                               empty     == ( (read_ptr + 1) == write_ptr )) )
    else $error("Read-only update error");

  // Write only: write_ptr advances, read_ptr holds, empty cleared, full set per design
  assert property ( (write && !full) && !(read && !empty) |=> (write_ptr == $past(write_ptr + 1) &&
                                                               read_ptr  == $past(read_ptr)      &&
                                                               empty     == 1'b0                  &&
                                                               full      == (read_ptr == (write_ptr + 1)) ) )
    else $error("Write-only update error");

  // Idle/no-ops (no effective read nor write): pointers hold
  assert property ( !(read && !empty) && !(write && !full) |=> (read_ptr  == $past(read_ptr) &&
                                                                write_ptr == $past(write_ptr)) )
    else $error("Pointers changed without read/write");

  // --------------------
  // Item out relation
  // --------------------
  // item_out is always the memory at read_ptr
  assert property ( item_out == memory[read_ptr] )
    else $error("item_out mismatch with memory[read_ptr]");

  // --------------------
  // Data-ordering and integrity scoreboard
  // --------------------
  bit [SIZE-1:0] refq[$];

  wire do_r = (read  && !empty);
  wire do_w = (write && !full);

  // Check read data matches queued write data and keep a reference level/flags model
  always @(posedge clk or posedge reset) begin
    if (reset) begin
      refq = {};
    end else begin
      // Check before mutating queue
      if (do_r) begin
        if (refq.size() == 0) $error("Underflow in reference model");
        else assert (item_out == refq[0]) else $error("Data mismatch on read");
      end

      // Update queue for simultaneous safely
      unique case ({do_r, do_w})
        2'b11: begin
          // Read then write: pop then push keeps depth stable
          void'(refq.pop_front());
          refq.push_back(item_in);
        end
        2'b10: void'(refq.pop_front());
        2'b01: refq.push_back(item_in);
        default: /* no-op */;
      endcase

      // Reference flags vs level
      assert (refq.size() <= DEPTH) else $error("Reference overflow");
      assert ( (refq.size()==0)     == empty ) else $error("Empty flag mismatch");
      assert ( (refq.size()==DEPTH) == full  ) else $error("Full flag mismatch");
      // When 0<level<DEPTH, neither empty nor full should be set
      if (refq.size() > 0 && refq.size() < DEPTH)
        assert (!empty && !full) else $error("Flags incorrect in mid-level");
    end
  end

  // --------------------
  // Coverage
  // --------------------
  // Reach empty after reset deassert
  cover property ( !reset ##1 empty );

  // Fill to full without reads
  sequence s_write_while_not_full;
    (write && !full)[*DEPTH];
  endsequence
  cover property ( s_write_while_not_full ##1 full );

  // Drain to empty without writes (only meaningful after full)
  sequence s_read_while_not_empty;
    (read && !empty)[*DEPTH];
  endsequence
  cover property ( full ##1 s_read_while_not_empty ##1 empty );

  // Simultaneous read and write in steady state (!full && !empty)
  cover property ( (!full && !empty) && read && write );

  // Pointer wrap-around on write_ptr and read_ptr
  if (DEPTH_LOG2 > 0) begin
    cover property ( (write && !full && $past(write_ptr) == {DEPTH_LOG2{1'b1}}) |=> (write_ptr == '0) );
    cover property ( (read  && !empty && $past(read_ptr)  == {DEPTH_LOG2{1'b1}}) |=> (read_ptr  == '0) );
  end

endmodule

bind fifo2 fifo2_sva #(.SIZE(SIZE), .DEPTH_LOG2(DEPTH_LOG2)) fifo2_sva_i
(
  .clk,
  .reset,
  .write,
  .read,
  .item_in,
  .item_out,
  .full,
  .empty
);