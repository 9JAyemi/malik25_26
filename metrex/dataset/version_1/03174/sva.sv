// SVA for jFIFO. Bind this checker to your DUT.
// Focus: correctness of flags, pointer updates, gating, memory/data integrity, and key coverage.

module jFIFO_sva #(
  parameter int DEPTH = 8,
  parameter int PTRW  = 3
)(
  input  logic               clock,
  input  logic               reset,
  input  logic               wn,
  input  logic               rn,
  input  logic [7:0]         DATAIN,
  input  logic [7:0]         DATAOUT,
  input  logic [PTRW-1:0]    wptr,
  input  logic [PTRW-1:0]    rptr,
  input  logic               full,
  input  logic               empty,
  input  logic [7:0]         memory [0:DEPTH-1]
);

  // Effective operations per RTL priority (write has priority over read)
  logic write_taken, read_taken;
  assign write_taken = wn && !full;
  assign read_taken  = (!write_taken) && rn && !empty;

  // Default clocking and reset masking for non-reset checks
  default clocking cb @(posedge clock); endclocking

  // Flag correctness (disable on Xs to avoid power-up glitches)
  assert property (@(cb) disable iff ($isunknown({wptr,rptr,full,empty}))
                   empty == (wptr == rptr))
    else $error("empty flag mismatch");

  assert property (@(cb) disable iff ($isunknown({wptr,rptr,full,empty}))
                   full  == ((wptr == 3'b111) && (rptr == 3'b000)))
    else $error("full flag mismatch");

  // Flags not both asserted
  assert property (@(cb) !(full && empty))
    else $error("full and empty both asserted");

  // Reset behavior (one cycle after a reset edge)
  assert property (@(cb) reset |=> (wptr==0 && rptr==0 && DATAOUT==8'h00 && empty && !full))
    else $error("reset state incorrect");

  for (genvar i=0; i<DEPTH; i++) begin : g_mem_reset
    assert property (@(cb) reset |=> (memory[i]==8'h00))
      else $error("memory[%0d] not cleared on reset", i);
  end

  // Pointer updates and stability
  assert property (@(cb) disable iff (reset) write_taken |=> (wptr == $past(wptr)+1))
    else $error("wptr did not increment on write");
  assert property (@(cb) disable iff (reset) read_taken  |=> (rptr == $past(rptr)+1))
    else $error("rptr did not increment on read");

  assert property (@(cb) disable iff (reset) !write_taken |=> (wptr == $past(wptr)))
    else $error("wptr changed without a write");
  assert property (@(cb) disable iff (reset) !read_taken  |=> (rptr == $past(rptr)))
    else $error("rptr changed without a read");

  // Priority: if both wn and rn true and both sides allowed, only write happens
  assert property (@(cb) disable iff (reset)
                   (wn && rn && !full && !empty) |=> (wptr==$past(wptr)+1 && rptr==$past(rptr)))
    else $error("read occurred when write should have priority");

  // Gating: no write when full; no read when empty (considering write priority)
  assert property (@(cb) disable iff (reset) (wn && full) |=> (wptr==$past(wptr)))
    else $error("write advanced while full");
  assert property (@(cb) disable iff (reset) (wn && full) |=> (memory[$past(wptr)]==$past(memory[$past(wptr)])))
    else $error("memory changed while full on write request");

  assert property (@(cb) disable iff (reset) (!write_taken && rn && empty) |=> (rptr==$past(rptr) && DATAOUT==$past(DATAOUT)))
    else $error("read advanced or DATAOUT changed while empty");

  // Data integrity: memory write and read dataout
  assert property (@(cb) disable iff (reset) write_taken |=> (memory[$past(wptr)] == $past(DATAIN)))
    else $error("memory write data mismatch");

  assert property (@(cb) disable iff (reset) read_taken  |=> (DATAOUT == $past(memory[$past(rptr)])))
    else $error("DATAOUT mismatch on read");

  // Stability when not updating
  for (genvar j=0; j<DEPTH; j++) begin : g_mem_stable
    assert property (@(cb) disable iff (reset) !write_taken |=> (memory[j]==$past(memory[j])))
      else $error("memory[%0d] changed without a write", j);
  end
  assert property (@(cb) disable iff (reset) !read_taken |=> (DATAOUT==$past(DATAOUT)))
    else $error("DATAOUT changed without a read");

  // Coverage
  cover property (@(cb) write_taken);
  cover property (@(cb) read_taken);
  cover property (@(cb) full);
  cover property (@(cb) empty);
  cover property (@(cb) disable iff (reset) (write_taken && ($past(wptr)==3'b111)) |=> (wptr==3'b000)); // wptr wrap
  cover property (@(cb) disable iff (reset) (read_taken  && ($past(rptr)==3'b111)) |=> (rptr==3'b000)); // rptr wrap
  cover property (@(cb) disable iff (reset) (wn && full));                                            // blocked write
  cover property (@(cb) disable iff (reset) (!write_taken && rn && empty));                           // blocked read
  cover property (@(cb) disable iff (reset) empty ##[1:$] full ##[1:$] empty);                        // empty->full->empty

endmodule

// Bind to all jFIFO instances
bind jFIFO jFIFO_sva #(.DEPTH(8), .PTRW(3)) u_jFIFO_sva (
  .clock(clock),
  .reset(reset),
  .wn(wn),
  .rn(rn),
  .DATAIN(DATAIN),
  .DATAOUT(DATAOUT),
  .wptr(wptr),
  .rptr(rptr),
  .full(full),
  .empty(empty),
  .memory(memory)
);