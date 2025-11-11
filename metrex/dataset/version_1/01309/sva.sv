// SVA for dpMem_dc: concise, high-signal-coverage, with a small shadow model.
// Bind this module to the DUT. Focus: address safety, X-propagation, sync behavior, and data integrity.

module dpMem_dc_sva #(
  parameter FIFO_WIDTH = 8,
  parameter FIFO_DEPTH = 64,
  parameter ADDR_WIDTH = 6
)(
  input wrClk,
  input rdClk,
  input [FIFO_WIDTH-1:0] dataIn,
  input [FIFO_WIDTH-1:0] dataOut,
  input writeEn,
  input readEn,
  input [ADDR_WIDTH-1:0] addrIn,
  input [ADDR_WIDTH-1:0] addrOut
);

  // Parameter sanity
  localparam int DEPTH_MAX = (1 << ADDR_WIDTH);
  initial assert (FIFO_DEPTH <= DEPTH_MAX)
    else $error("FIFO_DEPTH (%0d) exceeds addressable space (%0d)", FIFO_DEPTH, DEPTH_MAX);

  // Simple shadow model (NBA to match DUT NBA semantics and avoid same-cycle RD/WR races)
  bit [FIFO_WIDTH-1:0] ref_mem [0:FIFO_DEPTH-1];
  bit                  written [0:FIFO_DEPTH-1];

  always_ff @(posedge wrClk) begin
    if (writeEn && (addrIn < FIFO_DEPTH)) begin
      ref_mem[addrIn] <= dataIn;
      written[addrIn] <= 1'b1;
    end
  end

  default clocking cb @(posedge wrClk or posedge rdClk); endclocking

  // Address range checks
  assert property (@(posedge wrClk) writeEn |-> (addrIn < FIFO_DEPTH))
    else $error("Write address out of range: %0d", addrIn);

  assert property (@(posedge rdClk) (addrOut < FIFO_DEPTH))
    else $error("Read address out of range: %0d", addrOut);

  // X/Z checks on critical controls and buses when used
  assert property (@(posedge wrClk) !$isunknown(writeEn));
  assert property (@(posedge rdClk) !$isunknown(readEn));
  assert property (@(posedge wrClk) writeEn |-> !$isunknown({addrIn, dataIn}));
  assert property (@(posedge rdClk) !$isunknown(addrOut));

  // dataOut should only change on rdClk rising edge
  assert property (@(posedge wrClk or posedge rdClk) $changed(dataOut) |-> $rose(rdClk))
    else $error("dataOut changed without rdClk rising edge");

  // Functional correctness: read returns most recent written data to that address
  // Guarded by "written" to avoid asserting on uninitialized addresses.
  assert property (@(posedge rdClk)
                   (addrOut < FIFO_DEPTH && written[addrOut]) |-> (dataOut == ref_mem[addrOut]))
    else $error("Readback mismatch at addr %0d: got %0h exp %0h", addrOut, dataOut, ref_mem[addrOut]);

  // Lightweight coverage
  cover property (@(posedge wrClk) writeEn);                         // exercise writes
  cover property (@(posedge rdClk) written[addrOut]);                // read of initialized location
  cover property (@(posedge rdClk) written[addrOut] && dataOut == ref_mem[addrOut]); // correct readback
  cover property (@(posedge wrClk) writeEn && addrIn == '0);         // low address
  cover property (@(posedge wrClk) writeEn && addrIn == FIFO_DEPTH-1);
  cover property (@(posedge rdClk) addrOut == '0);
  cover property (@(posedge rdClk) addrOut == FIFO_DEPTH-1);

endmodule

// Bind into the DUT
bind dpMem_dc dpMem_dc_sva #(
  .FIFO_WIDTH(FIFO_WIDTH),
  .FIFO_DEPTH(FIFO_DEPTH),
  .ADDR_WIDTH(ADDR_WIDTH)
) dpMem_dc_sva_i (
  .wrClk(wrClk),
  .rdClk(rdClk),
  .dataIn(dataIn),
  .dataOut(dataOut),
  .writeEn(writeEn),
  .readEn(readEn),
  .addrIn(addrIn),
  .addrOut(addrOut)
);