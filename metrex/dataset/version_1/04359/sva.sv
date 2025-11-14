// SVA for splitter. Bind this module to the DUT to check/cover behavior.
module splitter_sva #(parameter int NUM_M=2) (
  input  logic                 clk,
  input  logic                 resetn,
  input  logic                 s_valid,
  input  logic [NUM_M-1:0]     m_ready,
  input  logic [NUM_M-1:0]     m_valid,
  input  logic                 s_ready,
  input  logic [NUM_M-1:0]     acked
);

  // Combinational relations must hold every cycle
  assert property (@(posedge clk) m_valid == (s_valid ? ~acked : '0))
    else $error("m_valid equation mismatch");
  assert property (@(posedge clk) s_ready == &(m_ready | acked))
    else $error("s_ready equation mismatch");

  // Reset behavior
  assert property (@(posedge clk) !resetn |-> (acked == '0))
    else $error("acked not cleared in reset");

  // Sequential update of acked
  assert property (@(posedge clk) disable iff (!resetn)
                   (s_valid && s_ready) |=> (acked == '0))
    else $error("acked not cleared after handshake");
  assert property (@(posedge clk) disable iff (!resetn)
                   !(s_valid && s_ready) |=> (acked == $past(acked | (m_ready & m_valid))))
    else $error("acked did not update as acked | (m_ready & m_valid)");

  // Sanity: m_valid cannot be asserted if s_valid is 0
  assert property (@(posedge clk) (|m_valid) |-> s_valid)
    else $error("m_valid asserted while s_valid=0");

  // X-propagation checks on outputs when out of reset
  assert property (@(posedge clk) disable iff (!resetn)
                   !$isunknown(s_ready) && !$isunknown(m_valid))
    else $error("X/Z detected on outputs");

  // Bit-level monotonicity and causality
  genvar i;
  generate
    for (i=0; i<NUM_M; i++) begin : g_bit
      // Acknowledgement can only rise due to prior ready&valid on that bit
      assert property (@(posedge clk) disable iff (!resetn)
                       $rose(acked[i]) |-> $past(m_ready[i] && m_valid[i]))
        else $error("acked[%0d] rose without prior m_ready&m_valid", i);
      // Acknowledgement can only fall due to a handshake (or reset which is disabled)
      assert property (@(posedge clk) disable iff (!resetn)
                       $fell(acked[i]) |-> $past(s_valid && s_ready))
        else $error("acked[%0d] fell without handshake", i);
    end
  endgenerate

  // Coverage
  // 1) Observe a handshake
  cover property (@(posedge clk) disable iff (!resetn) s_valid && s_ready);
  // 2) Multicycle fanout acceptance: backpressure followed by handshake
  cover property (@(posedge clk) disable iff (!resetn)
                  s_valid && !s_ready ##[1:$] s_valid && s_ready);
  // 3) Per-bit accept: bit 0 accepts and deasserts its m_valid next cycle
  if (NUM_M > 0) begin
    cover property (@(posedge clk) disable iff (!resetn)
                    s_valid && m_valid[0] && m_ready[0] ##1 acked[0] && !m_valid[0]);
  end

endmodule

// Example bind (place in a separate file or a package as appropriate):
// bind splitter splitter_sva #(.NUM_M(NUM_M)) u_splitter_sva (.* , .acked(acked));