// SVA checker for dma_request_generator
module dma_request_generator_sva #(
  parameter C_ID_WIDTH = 3,
  parameter C_BURSTS_PER_TRANSFER_WIDTH = 17
)(
  input  logic                          req_aclk,
  input  logic                          req_aresetn,
  input  logic                          req_valid,
  input  logic                          req_ready,
  input  logic [C_ID_WIDTH-1:0]         request_id,
  input  logic [C_ID_WIDTH-1:0]         response_id,
  input  logic [C_BURSTS_PER_TRANSFER_WIDTH-1:0] req_burst_count,
  input  logic                          enable,
  input  logic                          pause,
  input  logic                          eot,

  // Internal state (bind to DUT regs)
  input  logic [C_BURSTS_PER_TRANSFER_WIDTH-1:0] burst_count,
  input  logic [C_ID_WIDTH-1:0]                  id
);

  default clocking cb @(posedge req_aclk); endclocking
  default disable iff (!req_aresetn)

  // Combinational relations
  ap_eot_def:           assert property (eot == (burst_count == '0));
  ap_request_id_map:    assert property (request_id == id);

  // Reset values
  ap_reset_vals:        assert property (!req_aresetn |-> (req_ready && eot && request_id=='0 && burst_count=='0 && id=='0));

  // Enable low holds idle
  ap_enable_low_idle:   assert property ((req_aresetn && !enable) |=> (req_ready && $stable(id) && $stable(burst_count)));

  // Handshake load (accept request)
  ap_handshake_load:    assert property (req_ready && enable && req_valid
                                         |=> (!req_ready && burst_count == $past(req_burst_count) && $stable(id)));

  // Idle, no handshake => hold
  ap_idle_hold:         assert property (req_ready && (!req_valid || !enable)
                                         |=> (req_ready && $stable(id) && $stable(burst_count)));

  // Busy progress when not blocked by pause or response_id
  ap_busy_progress:     assert property (!req_ready && !pause && (response_id != (id + 1'b1)) && (burst_count != '0)
                                         |=> (id == $past(id) + 1 && burst_count == $past(burst_count) - 1 && !req_ready));

  // Busy, EOT reached and gate open => req_ready must reassert next
  ap_busy_eot_ready:    assert property (!req_ready && !pause && (response_id != (id + 1'b1)) && (burst_count == '0)
                                         |=> req_ready);

  // Busy but blocked => hold state
  ap_busy_block_hold:   assert property (!req_ready && (pause || (response_id == (id + 1'b1)))
                                         |=> ($stable(id) && $stable(burst_count) && !req_ready));

  // Sanity: do not underflow burst_count at EOT (will flag the current RTL bug)
  ap_no_underflow:      assert property (!req_ready && !pause && (response_id != (id + 1'b1)) && (burst_count == '0)
                                         |=> burst_count == '0)
                                         else $error("dma_request_generator: burst_count underflow at EOT");

  // Coverage

  // Typical transfer: accept, make progress for several beats, then finish
  sequence gate_open; !pause && (response_id != (id + 1'b1)); endsequence
  c_transfer:           cover property (req_ready && enable && req_valid
                                         ##1 !req_ready
                                         ##1 gate_open [*1:16]
                                         ##1 gate_open && (burst_count == '0)
                                         ##1 req_ready);

  // Pause stalls progress for at least 3 cycles
  c_pause_stall:        cover property (!req_ready ##1 pause [*3] ##1 gate_open ##1 1);

  // Response_id-match stalls progress for at least 3 cycles
  c_resp_match_stall:   cover property (!req_ready ##1 (response_id == (id + 1'b1)) [*3]
                                         ##1 (response_id != (id + 1'b1)) ##1 1);

  // ID wrap-around under progress
  c_id_wrap:            cover property (!req_ready && gate_open && (id == {C_ID_WIDTH{1'b1}})
                                         ##1 (id == '0));

  // Zero-length transfer acceptance and completion
  c_zero_len:           cover property (req_ready && enable && req_valid && (req_burst_count == '0)
                                         ##1 !req_ready
                                         ##1 gate_open
                                         ##1 req_ready);

endmodule

// Bind example (place in a testbench or a separate bind file)
bind dma_request_generator
  dma_request_generator_sva #(
    .C_ID_WIDTH(C_ID_WIDTH),
    .C_BURSTS_PER_TRANSFER_WIDTH(C_BURSTS_PER_TRANSFER_WIDTH)
  ) dma_request_generator_sva_i (
    .req_aclk(req_aclk),
    .req_aresetn(req_aresetn),
    .req_valid(req_valid),
    .req_ready(req_ready),
    .request_id(request_id),
    .response_id(response_id),
    .req_burst_count(req_burst_count),
    .enable(enable),
    .pause(pause),
    .eot(eot),
    .burst_count(burst_count), // internal
    .id(id)                    // internal
  );