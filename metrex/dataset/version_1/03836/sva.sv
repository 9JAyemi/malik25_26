// SVA checker for ram16b: functional scoreboard, CDC-safe checks, concise coverage
// Bind this file to the design (no DUT changes required).

module ram16b_sva #(parameter ADDR_W=5, DATA_W=16, DEPTH=(1<<ADDR_W)) (
  input  logic                 wclk,
  input  logic                 rclk,
  input  logic                 wen,
  input  logic [ADDR_W-1:0]    waddr,
  input  logic [DATA_W-1:0]    wdata,
  input  logic [ADDR_W-1:0]    raddr,
  input  logic [DATA_W-1:0]    rdata
);
  // Simple golden model (multi-clock safe)
  logic [DATA_W-1:0] sb_mem   [DEPTH];
  bit                sb_valid [DEPTH];
  int unsigned       seq      [DEPTH];

  // Seen a clock pulse flags to guard $past()
  bit rclk_seen, wclk_seen;

  initial begin
    foreach (sb_valid[i]) sb_valid[i] = 0;
    foreach (seq[i])      seq[i]      = 0;
    rclk_seen = 0;
    wclk_seen = 0;
  end

  always_ff @(posedge wclk) wclk_seen <= 1'b1;
  always_ff @(posedge rclk) rclk_seen <= 1'b1;

  // Update model on writes
  always_ff @(posedge wclk) begin
    // Basic input sanity when used
    if (wen) begin
      // Avoid poisoning the model with X
      assume (!$isunknown(waddr));
      assume (!$isunknown(wdata));
      sb_mem[waddr]  <= wdata;
      sb_valid[waddr]<= 1'b1;
      seq[waddr]     <= seq[waddr] + 1;
    end
    // Control should not be X at active edge
    assume (!$isunknown(wen));
  end

  // Snapshot for "no intervening writes" stability check
  logic [ADDR_W-1:0] raddr_q;
  int unsigned       seq_q;
  logic [DATA_W-1:0] rdata_q;

  always_ff @(posedge rclk) begin
    raddr_q <= raddr;
    seq_q   <= seq[raddr];
    rdata_q <= rdata;
    // Read-side controls should not be X at active edge
    assume (!$isunknown(raddr));
  end

  // Read must return last written value (1 rclk latency due to registered address)
  property p_read_matches_model;
    @(posedge rclk) disable iff (!rclk_seen)
      !$isunknown($past(raddr)) && sb_valid[$past(raddr)]
      |-> rdata == sb_mem[$past(raddr)];
  endproperty
  assert property (p_read_matches_model);

  // Read data should be known for addresses that have been written
  property p_read_known_when_valid;
    @(posedge rclk) disable iff (!rclk_seen)
      !$isunknown($past(raddr)) && sb_valid[$past(raddr)]
      |-> !$isunknown(rdata);
  endproperty
  assert property (p_read_known_when_valid);

  // If address is unchanged and there were no writes to that address between rclk edges,
  // the read data must remain stable
  property p_rdata_stable_no_writes;
    @(posedge rclk) disable iff (!rclk_seen)
      (raddr == raddr_q) && (seq[raddr] == seq_q) |-> rdata == rdata_q;
  endproperty
  assert property (p_rdata_stable_no_writes);

  // Optional: write/read basic protocol sanity
  // Write data should be stable within the wclk sampling when wen is asserted
  property p_write_bus_known;
    @(posedge wclk) wen |-> (!$isunknown(waddr) && !$isunknown(wdata));
  endproperty
  assert property (p_write_bus_known);

  // Coverage: observe writes and valid reads, and read-after-write to same addr
  cover property (@(posedge wclk) wen);
  cover property (@(posedge rclk) disable iff (!rclk_seen) sb_valid[$past(raddr)]);

  // Read-after-write (eventually) to same address returns the written data
  // This covers cross-clock interaction without over-constraining timing
  sequence s_write(addr, data);
    @(posedge wclk) wen && (waddr==addr) && (wdata==data);
  endsequence
  property p_raw_cover;
    // After a write to some address, eventually a read of that address matches the model
    logic [ADDR_W-1:0] a;
    logic [DATA_W-1:0] d;
    (s_write(a,d), a=waddr, d=wdata)
      ##[1:$] @(posedge rclk)
      (raddr == $past(a,0)) && sb_valid[$past(raddr)]
      ##0 (rdata == sb_mem[raddr]);
  endproperty
  cover property (p_raw_cover);

endmodule

// Bind to the top-level wrapper so it works for both sim and synth variants
bind ram16b ram16b_sva #(.ADDR_W(5), .DATA_W(16)) i_ram16b_sva (
  .wclk(wclk),
  .rclk(rclk),
  .wen(wen),
  .waddr(waddr),
  .wdata(wdata),
  .raddr(raddr),
  .rdata(rdata)
);