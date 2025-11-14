// SVA for axi_data_mover
// Bind into the DUT for in-context access to internal signals
module axi_data_mover_sva #(parameter int MAX_BEATS_PER_BURST = 16) ();
  // These names resolve in the bound instance scope
  default clocking cb @(posedge clk); endclocking
  default disable iff (!resetn);

  // Basic combinational relationships
  assert property (xfer_req == active);
  assert property (response_id == id);
  assert property (s_axi_ready == (m_axi_ready & pending_burst & active));
  assert property (m_axi_valid == (s_axi_valid & pending_burst & active));
  assert property (m_axi_data  == s_axi_data);
  assert property (m_axi_last  == (eot ? last_eot : last_non_eot));
  assert property (last        == (eot ? last_eot : last_non_eot));
  assert property (last_load   == ((m_axi_ready & s_axi_valid & active) & (last_eot | last_non_eot)));
  // Enabled mirrors enable with reset dominance
  assert property (@(posedge clk) enabled == (resetn && enable));

  // Ready/valid cannot assert when not in an active pending burst
  assert property ((!active || !pending_burst) |-> (!s_axi_ready && !m_axi_valid));
  // Gated valid/ready implications
  assert property (m_axi_valid |-> s_axi_valid);
  assert property (s_axi_ready |-> m_axi_ready);

  // req_ready policy implemented by DUT
  assert property (req_ready == (active || !req_valid));

  // Request acceptance initializes state (as per DUT behavior)
  assert property ((req_valid && !active)
                   |=> (active && pending_burst && (beat_counter == 4'd1)
                        && (last_burst_length == $past(req_last_burst_length))
                        && (id_next == $past(id)+3'd1)));

  // ID increments only when a request is accepted
  assert property ($changed(id) |-> $past(req_valid && !active));

  // Transfer handshake
  sequence xfer; s_axi_valid && s_axi_ready; endsequence

  // Beat counter increments on each transfer beat
  assert property (xfer |=> (beat_counter == $past(beat_counter) + 4'd1));

  // Last flag generation (registered one cycle after qualifying beat)
  assert property (xfer && (beat_counter == last_burst_length)
                   |=> (last_eot && !last_non_eot));
  assert property (xfer && (beat_counter == (MAX_BEATS_PER_BURST-1))
                   |=> (last_non_eot && !last_eot));
  assert property (xfer && (beat_counter != last_burst_length)
                        && (beat_counter != (MAX_BEATS_PER_BURST-1))
                   |=> (!last_eot && !last_non_eot));
  // Mutually exclusive last flags
  assert property (!(last_eot && last_non_eot));

  // m_axi_last must mark the actual last beat on the same cycle as the beat transfers
  assert property (xfer
                   |-> (m_axi_last ==
                        (eot ? (beat_counter == last_burst_length)
                             : (beat_counter == (MAX_BEATS_PER_BURST-1)))));

  // Transfer must terminate immediately after a last beat handshake
  assert property (xfer && m_axi_last |=> (!active && !pending_burst));

  // Coverage
  // Request accepted
  cover property (req_valid && !active);
  // Backpressure case observed
  cover property (s_axi_valid && !m_axi_ready && (!s_axi_ready));
  // Non-EOT boundary termination (burst boundary)
  cover property (xfer && (beat_counter == (MAX_BEATS_PER_BURST-1)) && !eot ##0 m_axi_last);
  // EOT termination before boundary
  cover property (xfer && (beat_counter == last_burst_length) && eot ##0 m_axi_last);
  // req_ready deassert scenario
  cover property (req_valid && !active && !req_ready);
  // last_load occurrence
  cover property (last_load);

endmodule

bind axi_data_mover axi_data_mover_sva #(.MAX_BEATS_PER_BURST(MAX_BEATS_PER_BURST)) i_axi_data_mover_sva();