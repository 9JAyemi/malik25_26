// SVA for dpram: concise, high-quality checks and coverage.
// Bind this file to the DUT.
// Focus: address legality, X-checks, 1-cycle read latency across async clocks,
// stability when no intervening write, and key scenario coverage.

module dpram_sva #(parameter depth = 4,
                   parameter width = 16,
                   parameter size  = 16)
(
  input wclk,
  input [width-1:0] wdata,
  input [depth-1:0] waddr,
  input             wen,

  input rclk,
  input [width-1:0] rdata,
  input [depth-1:0] raddr
);

  // Simple shadow model to define expected behavior
  logic [width-1:0] ref_mem [0:size-1];
  int unsigned wtag [0:size-1]; // per-address write counter to detect intervening writes

  // Initialize tags to zero (ref_mem values are don't-care until read pipeline warms)
  initial begin
    for (int i = 0; i < size; i++) begin
      wtag[i] = 0;
    end
  end

  // Update reference model on writes that are in range
  always @(posedge wclk) begin
    if (wen && (waddr < size)) begin
      ref_mem[waddr] <= wdata;
      wtag[waddr]    <= wtag[waddr] + 1;
    end
  end

  // Simple rclk-cycle counter to gate assertions during pipeline warm-up
  int unsigned rclk_edges = 0;
  always @(posedge rclk) if (rclk_edges < 2) rclk_edges++;

  // ---------------------------------------------------------------------------
  // Safety / Sanity assertions
  // ---------------------------------------------------------------------------

  // Parameter sanity (static)
  initial begin
    if (size > (1<<depth)) $error("dpram: size (%0d) exceeds addressable range by depth (%0d)", size, depth);
  end

  // No X/Z on critical inputs at their use points
  a_w_inputs_known: assert property (@(posedge wclk)
    !$isunknown(wen) &&
    (!wen || (!$isunknown(waddr) && !$isunknown(wdata))))
    else $error("dpram: X/Z on write-side inputs");

  a_raddr_known: assert property (@(posedge rclk)
    !$isunknown(raddr))
    else $error("dpram: X/Z on read address");

  // Address range checks
  a_waddr_in_range: assert property (@(posedge wclk)
    !wen or (waddr < size))
    else $error("dpram: write address out of range: %0d", waddr);

  a_raddr_in_range: assert property (@(posedge rclk)
    raddr < size)
    else $error("dpram: read address out of range: %0d", raddr);

  // Optional: rdata should not be X after pipeline has at least 1 cycle
  a_rdata_known: assert property (@(posedge rclk)
    (rclk_edges < 1) or !$isunknown(rdata))
    else $error("dpram: X/Z on rdata");

  // ---------------------------------------------------------------------------
  // Functional assertions
  // ---------------------------------------------------------------------------

  // 1-cycle read latency w.r.t. rclk:
  // rdata at current rclk equals memory content addressed at the previous rclk.
  a_read_latency_and_value: assert property (@(posedge rclk)
    (rclk_edges < 1) or (rdata == $past(ref_mem[$past(raddr)])))
    else $error("dpram: rdata mismatch vs. expected 1-cycle-latency memory value");

  // If raddr is unchanged and no write to that address occurred between rclk edges,
  // rdata must hold its previous value.
  a_read_stable_no_write: assert property (@(posedge rclk)
    (rclk_edges < 2) or
    ((raddr == $past(raddr)) &&
     (wtag[raddr] == $past(wtag[$past(raddr)]))) |-> (rdata == $past(rdata)))
    else $error("dpram: rdata changed without intervening write to same address");

  // ---------------------------------------------------------------------------
  // Coverage: key scenarios
  // ---------------------------------------------------------------------------

  // Any write and read activity
  c_write: cover property (@(posedge wclk) wen);
  c_read:  cover property (@(posedge rclk) 1);

  // Boundary addresses written
  c_write_addr0:      cover property (@(posedge wclk) wen && (waddr == 0));
  c_write_addr_last:  cover property (@(posedge wclk) wen && (waddr == size-1));

  // Back-to-back writes to same address
  c_b2b_same_addr: cover property (@(posedge wclk) wen && $past(wen) && (waddr == $past(waddr)));

  // Read-after-write to same address across clocks (write precedes read)
  c_raw_same_addr: cover property (@(posedge rclk)
    $past(wen, 1, wclk) && (raddr == $past(waddr, 1, wclk)));

  // Coincident read and write to same address (both clocks rise in same timestep)
  c_coincident_rw: cover property (@(posedge wclk)
    wen && $rose(rclk) && (waddr == raddr));

  // Read two consecutive cycles from same address with an intervening write to that address
  c_read_write_between_reads: cover property (@(posedge rclk)
    (rclk_edges >= 2) &&
    (raddr == $past(raddr)) &&
    (wtag[raddr] != $past(wtag[$past(raddr)])));

endmodule

// Bind into the DUT
bind dpram dpram_sva #(.depth(depth), .width(width), .size(size))
  dpram_sva_i(.wclk(wclk), .wdata(wdata), .waddr(waddr), .wen(wen),
              .rclk(rclk), .rdata(rdata), .raddr(raddr));