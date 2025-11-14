// SVA for axi_data_transfer
// Bind-ready, concise, high-signal-quality checks and useful coverage.

checker axi_data_transfer_sva #(
  parameter int C_ID_WIDTH = 3,
  parameter int C_DATA_WIDTH = 64,
  parameter bit C_DISABLE_WAIT_FOR_ID = 1
)(
  input logic                         clk,
  input logic                         resetn,

  // DUT ports
  input  logic [C_ID_WIDTH-1:0]       request_id,
  input  logic [C_ID_WIDTH-1:0]       response_id,
  input  logic                        sync_id,
  input  logic                        eot,

  input  logic                        enable,
  input  logic                        enabled,

  input  logic                        s_axi_ready,
  input  logic                        s_axi_valid,
  input  logic [C_DATA_WIDTH-1:0]     s_axi_data,

  input  logic                        m_axi_ready,
  input  logic                        m_axi_valid,
  input  logic [C_DATA_WIDTH-1:0]     m_axi_data,
  input  logic                        m_axi_last,

  input  logic                        req_valid,
  input  logic                        req_ready,
  input  logic [3:0]                  req_last_burst_length,

  // DUT internals (hooked by bind)
  input  logic [3:0]                  beat_counter,
  input  logic [3:0]                  last_burst_length,
  input  logic [C_ID_WIDTH-1:0]       id,
  input  logic                        pending_burst
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!resetn)

  // Basic X checks on critical outputs and state
  assert property (!$isunknown({enabled, req_ready, s_axi_ready, m_axi_valid, m_axi_last, response_id})));
  assert property (!$isunknown({pending_burst, id})));

  // Combinational equivalences
  assert property (s_axi_ready == (m_axi_ready & pending_burst & ~req_ready));
  assert property (m_axi_valid == (s_axi_valid & pending_burst & ~req_ready));
  assert property (m_axi_data  ==  s_axi_data);
  assert property (m_axi_last  == (beat_counter == (eot ? last_burst_length : 4'hf)));
  assert property (response_id == id);
  assert property (pending_burst == (id != request_id));

  // Handshake implications
  assert property (s_axi_ready |-> m_axi_ready);
  assert property (s_axi_ready |-> (m_axi_valid == s_axi_valid));
  assert property ((!pending_burst || req_ready) |-> (!s_axi_ready && !m_axi_valid));

  // Request accept and counters
  assert property (req_ready && req_valid && enabled |=> !req_ready && (beat_counter == 4'h0) && (last_burst_length == $past(req_last_burst_length)));
  assert property (req_ready && req_valid && !enabled |=> req_ready); // ignore when not enabled
  assert property (!req_ready && (s_axi_ready && s_axi_valid) |=> beat_counter == $past(beat_counter) + 1);
  assert property (!req_ready && !(s_axi_ready && s_axi_valid) |=> beat_counter == $past(beat_counter));
  assert property (!enabled |=> req_ready); // deasserted enables force req_ready high next cycle
  assert property (req_ready |-> !s_axi_ready); // cannot source data while waiting for request

  // End-of-transfer behavior
  assert property ((s_axi_ready && s_axi_valid && (beat_counter == (eot ? last_burst_length : 4'hf)) && eot) |=> req_ready));
  assert property ((s_axi_ready && s_axi_valid && (beat_counter == (eot ? last_burst_length : 4'hf)) && !eot) |=> !req_ready));

  // ID/progress behavior
  assert property (((s_axi_ready && s_axi_valid && (beat_counter == (eot ? last_burst_length : 4'hf))) || (sync_id && (id != request_id))) |=> id == $past(id) + 1));
  assert property (!((s_axi_ready && s_axi_valid && (beat_counter == (eot ? last_burst_length : 4'hf))) || (sync_id && (id != request_id))) |=> id == $past(id));

  // Enabled control behavior
  assert property (enable |=> enabled);
  if (!C_DISABLE_WAIT_FOR_ID) begin
    // Must finish current beat before disabling
    assert property (!enable && s_axi_valid && !m_axi_ready |=> enabled);
    assert property (!enable && (!s_axi_valid || m_axi_ready) |=> !enabled);
  end else begin
    // Must complete all pending bursts (id must catch up)
    assert property (!enable && (response_id != request_id) |=> enabled);
    assert property (!enable && (response_id == request_id) |=> !enabled);
  end

  // last_burst_length changes only on request accept
  assert property ((last_burst_length != $past(last_burst_length)) |-> $past(req_ready && req_valid && enabled));

  // Coverage
  cover property (req_ready && req_valid && enabled ##1 !req_ready ##[1:32] (s_axi_ready && s_axi_valid && eot && m_axi_last) ##1 req_ready);
  cover property (req_ready && req_valid && enabled ##1 !req_ready ##[1:32] (s_axi_ready && s_axi_valid && !eot && m_axi_last));
  cover property (sync_id && (id != request_id) && !(s_axi_ready && s_axi_valid) ##1 (id == $past(id)+1));
  if (!C_DISABLE_WAIT_FOR_ID) begin
    cover property (!enable && (s_axi_valid || m_axi_ready) ##1 !enabled);
  end else begin
    cover property (!enable && (response_id != request_id) ##[1:16] (response_id == request_id) ##1 !enabled);
  end

endchecker

// Bind this checker to the DUT
bind axi_data_transfer axi_data_transfer_sva #(
  .C_ID_WIDTH(C_ID_WIDTH),
  .C_DATA_WIDTH(C_DATA_WIDTH),
  .C_DISABLE_WAIT_FOR_ID(C_DISABLE_WAIT_FOR_ID)
) axi_data_transfer_sva_i (
  .clk(clk),
  .resetn(resetn),
  .request_id(request_id),
  .response_id(response_id),
  .sync_id(sync_id),
  .eot(eot),
  .enable(enable),
  .enabled(enabled),
  .s_axi_ready(s_axi_ready),
  .s_axi_valid(s_axi_valid),
  .s_axi_data(s_axi_data),
  .m_axi_ready(m_axi_ready),
  .m_axi_valid(m_axi_valid),
  .m_axi_data(m_axi_data),
  .m_axi_last(m_axi_last),
  .req_valid(req_valid),
  .req_ready(req_ready),
  .req_last_burst_length(req_last_burst_length),
  .beat_counter(beat_counter),
  .last_burst_length(last_burst_length),
  .id(id),
  .pending_burst(pending_burst)
);