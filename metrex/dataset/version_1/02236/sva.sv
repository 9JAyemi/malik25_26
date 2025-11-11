// SVA checker for dmac_2d_transfer
// Bind this checker to the DUT instance.
// Focused on protocol, sequencing, address/length progression, IDs, and EOT behavior.

module dmac_2d_transfer_sva #(
  parameter int C_DMA_LENGTH_WIDTH = 24,
  parameter int C_ADDR_ALIGN_BITS  = 3
)(
  // clock/reset
  input  logic                           req_aclk,
  input  logic                           req_aresetn,

  // req side
  input  logic                           req_valid,
  input  logic                           req_ready,
  input  logic [31:C_ADDR_ALIGN_BITS]    req_dest_address,
  input  logic [31:C_ADDR_ALIGN_BITS]    req_src_address,
  input  logic [C_DMA_LENGTH_WIDTH-1:0]  req_x_length,
  input  logic [C_DMA_LENGTH_WIDTH-1:0]  req_y_length,
  input  logic [C_DMA_LENGTH_WIDTH-1:0]  req_dest_stride,
  input  logic [C_DMA_LENGTH_WIDTH-1:0]  req_src_stride,
  input  logic                           req_sync_transfer_start,
  input  logic                           req_eot,

  // out req side
  input  logic                           out_req_valid,
  input  logic                           out_req_ready,
  input  logic [31:C_ADDR_ALIGN_BITS]    out_req_dest_address,
  input  logic [31:C_ADDR_ALIGN_BITS]    out_req_src_address,
  input  logic [C_DMA_LENGTH_WIDTH-1:0]  out_req_length,
  input  logic                           out_req_sync_transfer_start,

  // eot return
  input  logic                           out_eot,

  // internal state tapped for stronger checks
  input  logic [C_DMA_LENGTH_WIDTH-1:0]  x_length,
  input  logic [C_DMA_LENGTH_WIDTH-1:0]  y_length,
  input  logic [C_DMA_LENGTH_WIDTH-1:0]  dest_stride,
  input  logic [C_DMA_LENGTH_WIDTH-1:0]  src_stride,
  input  logic [1:0]                     req_id,
  input  logic [1:0]                     eot_id
);

  default clocking cb @(posedge req_aclk); endclocking

  // Basic reset state on outputs
  assert property (disable iff (1'b0)
    !req_aresetn |-> (req_ready && !out_req_valid && !out_req_sync_transfer_start && !req_eot)
  );

  // out_req_valid cannot coincide with req_ready
  assert property (disable iff (!req_aresetn)
    !(out_req_valid && req_ready)
  );

  // Accept handshake loads and drives next cycle
  assert property (disable iff (!req_aresetn)
    (req_valid && req_ready) |=> (out_req_valid && !req_ready &&
                                  out_req_dest_address == $past(req_dest_address) &&
                                  out_req_src_address  == $past(req_src_address)  &&
                                  out_req_length       == $past(req_x_length)     &&
                                  out_req_sync_transfer_start == $past(req_sync_transfer_start))
  );

  // out_req_valid rises only due to accept
  assert property (disable iff (!req_aresetn)
    $rose(out_req_valid) |-> $past(req_valid && req_ready)
  );

  // While stalled, hold all request fields stable
  assert property (disable iff (!req_aresetn)
    (out_req_valid && !out_req_ready) |=> (out_req_valid &&
                                           $stable(out_req_dest_address) &&
                                           $stable(out_req_src_address)  &&
                                           $stable(out_req_length)       &&
                                           $stable(out_req_sync_transfer_start))
  );

  // Length wiring: out_req_length equals internal x_length during active transfer
  assert property (disable iff (!req_aresetn)
    out_req_valid |-> (out_req_length == x_length)
  );

  // x_length stable across the transfer lifetime
  assert property (disable iff (!req_aresetn)
    !req_ready |-> $stable(x_length)
  );

  // Address progression per handshake (uses stride >> C_ADDR_ALIGN_BITS)
  assert property (disable iff (!req_aresetn)
    (out_req_valid && out_req_ready) |=> (
      out_req_dest_address == $past(out_req_dest_address) + $past(dest_stride[C_DMA_LENGTH_WIDTH-1:C_ADDR_ALIGN_BITS]) &&
      out_req_src_address  == $past(out_req_src_address)  + $past(src_stride [C_DMA_LENGTH_WIDTH-1:C_ADDR_ALIGN_BITS])
    )
  );

  // y_length decrements each handshake
  assert property (disable iff (!req_aresetn)
    (out_req_valid && out_req_ready) |=> (y_length == $past(y_length) - 1)
  );

  // End-of-transfer for the request: out_req_valid drops only after a last handshake (y_length==0 in prior cycle)
  assert property (disable iff (!req_aresetn)
    $fell(out_req_valid) |-> $past(out_req_valid && out_req_ready && (y_length == 0))
  );

  // req_ready rises only when completing the last beat
  assert property (disable iff (!req_aresetn)
    $rose(req_ready) |-> $past(out_req_valid && out_req_ready && (y_length == 0))
  );

  // While a transfer is active, req_ready must stay low
  assert property (disable iff (!req_aresetn)
    out_req_valid |-> !req_ready
  );

  // sync_transfer_start behavior
  assert property (disable iff (!req_aresetn)
    !out_req_valid |-> !out_req_sync_transfer_start
  );
  assert property (disable iff (!req_aresetn)
    (out_req_sync_transfer_start && out_req_valid && out_req_ready) |=> !out_req_sync_transfer_start
  );

  // EOT signaling: only with out_eot, single-cycle pulse, and never when no out_eot
  assert property (disable iff (!req_aresetn)
    req_eot |-> out_eot
  );
  assert property (disable iff (!req_aresetn)
    !out_eot |-> !req_eot
  );
  assert property (disable iff (!req_aresetn)
    req_eot |=> !req_eot
  );

  // ID counters monotonic on their respective events (mod-4)
  assert property (disable iff (!req_aresetn)
    (out_req_valid && out_req_ready) |=> (req_id == $past(req_id) + 1)
  );
  assert property (disable iff (!req_aresetn)
    out_eot |=> (eot_id == $past(eot_id) + 1)
  );

  // Outstanding tracking (environment must not overflow 2-bit ID space)
  int outstanding;
  always_ff @(posedge req_aclk or negedge req_aresetn) begin
    if (!req_aresetn) begin
      outstanding <= 0;
    end else begin
      unique case ({out_req_valid && out_req_ready, out_eot})
        2'b10: outstanding <= outstanding + 1;
        2'b01: outstanding <= outstanding - 1;
        2'b11: outstanding <= outstanding; // issue and retire in same cycle
        default: /* no change */ ;
      endcase
      assert (outstanding >= 0) else $error("Negative outstanding");
      assert (outstanding <= 4) else $error("Outstanding > 4 overflows 2-bit ID");
      assert (!(out_eot && (outstanding == 0))) else $error("out_eot with no outstanding");
    end
  end

  // Coverage
  sequence s_accept;  req_valid && req_ready; endsequence
  sequence s_hs;      out_req_valid && out_req_ready; endsequence

  cover property (disable iff (!req_aresetn)
    s_accept ##1 out_req_valid
  );

  // Multi-row transfer: at least two handshakes before out_req_valid drops
  cover property (disable iff (!req_aresetn)
    s_accept ##1 s_hs ##1 !s_hs[*1:$] ##1 s_hs ##1 $fell(out_req_valid)
  );

  // Single-row transfer: out_req_valid drops right after first handshake
  cover property (disable iff (!req_aresetn)
    s_accept ##1 s_hs ##1 $fell(out_req_valid)
  );

  // Backpressure: valid held while !ready
  cover property (disable iff (!req_aresetn)
    s_accept ##1 out_req_valid && !out_req_ready ##[2:10] s_hs
  );

  // Reach max outstanding depth
  cover property (disable iff (!req_aresetn)
    outstanding == 4
  );

  // req_eot pulse observed
  cover property (disable iff (!req_aresetn)
    out_eot && req_eot
  );

endmodule

// Example bind (instantiate this in your testbench or a package):
// bind dmac_2d_transfer dmac_2d_transfer_sva #(
//   .C_DMA_LENGTH_WIDTH(C_DMA_LENGTH_WIDTH),
//   .C_ADDR_ALIGN_BITS (C_ADDR_ALIGN_BITS)
// ) u_dmac_2d_transfer_sva (
//   .req_aclk(req_aclk), .req_aresetn(req_aresetn),
//   .req_valid(req_valid), .req_ready(req_ready),
//   .req_dest_address(req_dest_address), .req_src_address(req_src_address),
//   .req_x_length(req_x_length), .req_y_length(req_y_length),
//   .req_dest_stride(req_dest_stride), .req_src_stride(req_src_stride),
//   .req_sync_transfer_start(req_sync_transfer_start),
//   .req_eot(req_eot),
//   .out_req_valid(out_req_valid), .out_req_ready(out_req_ready),
//   .out_req_dest_address(out_req_dest_address), .out_req_src_address(out_req_src_address),
//   .out_req_length(out_req_length), .out_req_sync_transfer_start(out_req_sync_transfer_start),
//   .out_eot(out_eot),
//   // internal taps
//   .x_length(x_length), .y_length(y_length),
//   .dest_stride(dest_stride), .src_stride(src_stride),
//   .req_id(req_id), .eot_id(eot_id)
// );