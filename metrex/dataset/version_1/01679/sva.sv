// SVA checker for small_fifo_a_dpfifo
// Bind this checker to the DUT. Focused, high-signal-coverage, concise.

module small_fifo_a_dpfifo_sva #(int DEPTH=8, int DW=72, int AW=3) (
  input  logic              clock,
  input  logic              sclr,
  input  logic              wreq,
  input  logic              rreq,
  input  logic              full,
  input  logic              empty,
  input  logic [DW-1:0]     data,
  input  logic [DW-1:0]     q,
  input  logic [AW-1:0]     usedw
);
  default clocking cb @(posedge clock); endclocking
  default disable iff (sclr);

  // Handshake qualifies (DUT semantics)
  logic wen, ren;
  always_comb begin
    wen = wreq && !full;
    ren = rreq && !empty;
  end

  // Simple scoreboard/model for FIFO behavior
  logic [DW-1:0] m_q[$];        // model queue
  logic [DW-1:0] exp_head;      // expected front data
  int unsigned   m_occ;

  // Model update (not disabled on reset so it reinitializes)
  always_ff @(posedge clock) begin
    if (sclr) begin
      m_q.delete();
      m_occ <= 0;
    end else begin
      if (wen) m_q.push_back(data);
      if (ren && m_q.size()>0) void'(m_q.pop_front());
      m_occ <= m_q.size();
    end
  end

  always_comb exp_head = (m_q.size()>0) ? m_q[0] : 'x;

  // Reset/post-reset checks
  // After a reset cycle, flags and counters must be in reset state.
  assert property (sclr |=> empty && !full && usedw==0)
    else $error("Reset values incorrect");

  // Occupancy accounting vs usedw
  // usedw must track true occupancy and stay within [0, DEPTH]
  assert property (usedw == m_occ)
    else $error("usedw mismatch vs model occupancy");
  assert property (usedw <= DEPTH)
    else $error("usedw exceeded DEPTH");
  assert property ( (usedw==0) == empty )
    else $error("empty flag inconsistent with usedw");
  assert property ( (usedw==DEPTH) == full )
    else $error("full flag inconsistent with usedw");

  // Monotonicity and simultaneous R/W semantics
  assert property ( wen && !ren |=> usedw == $past(usedw)+1 )
    else $error("usedw did not increment on write");
  assert property ( !wen && ren |=> usedw == $past(usedw)-1 )
    else $error("usedw did not decrement on read");
  assert property ( wen && ren |=> usedw == $past(usedw) )
    else $error("usedw changed on simultaneous read+write");

  // Illegal operations blocked (no effect without opposite op)
  assert property ( full && wreq && !ren |=> usedw == $past(usedw) && full )
    else $error("Write had effect while full without concurrent read");
  assert property ( empty && rreq && !wen |=> usedw == $past(usedw) && empty )
    else $error("Read had effect while empty without concurrent write");

  // Data integrity (FIFO ordering)
  // On a valid read, q must equal the model front.
  assert property ( ren |-> (q === exp_head) )
    else $error("q does not match expected FIFO head on read");

  // When writing to an empty FIFO (no concurrent read), next q must reflect that write.
  assert property ( $past(wen && !$past(ren) && $past(empty)) |-> q == $past(data) )
    else $error("q did not update with first written data when FIFO was empty");

  // Basic coverage
  cover property ( !sclr ##1 empty ##1 wen [*DEPTH] ##1 full );                 // reach full
  cover property ( !sclr ##1 full ##1 ren ##1 !full );                          // exit full on read
  cover property ( !sclr ##1 empty ##1 wen ##1 !empty );                        // exit empty on write
  cover property ( !sclr ##1 wen && ren );                                      // simultaneous R/W
  cover property ( !sclr ##1 (usedw==DEPTH-1) ##1 wen ##1 full );               // fill boundary
  cover property ( !sclr ##1 (usedw==1) ##1 ren ##1 empty );                    // drain boundary

endmodule

// Bind to DUT
bind small_fifo_a_dpfifo small_fifo_a_dpfifo_sva #(.DEPTH(8), .DW(72), .AW(3)) fifo_chk (
  .clock(clock),
  .sclr(sclr),
  .wreq(wreq),
  .rreq(rreq),
  .full(full),
  .empty(empty),
  .data(data),
  .q(q),
  .usedw(usedw)
);