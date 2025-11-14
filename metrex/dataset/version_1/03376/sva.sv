// SVA for sync_bits
module sync_bits_sva #(
  parameter int NUM_OF_BITS = 1,
  parameter bit ASYNC_CLK   = 1
)(
  input  logic [NUM_OF_BITS-1:0] in,
  input  logic                   out_resetn,
  input  logic                   out_clk,
  input  logic [NUM_OF_BITS-1:0] out,
  input  logic [NUM_OF_BITS-1:0] cdc_sync_stage1,
  input  logic [NUM_OF_BITS-1:0] cdc_sync_stage2
);

  default clocking cb @(posedge out_clk); endclocking

  // Reset drives stages to 0; in ASYNC mode, out must be 0 in reset
  assert property ( !out_resetn |-> (cdc_sync_stage1 == '0 && cdc_sync_stage2 == '0) );
  if (ASYNC_CLK) begin
    assert property ( !out_resetn |-> (out == '0) );
  end

  // No X/Z on output when out of reset
  assert property ( disable iff (!out_resetn) !$isunknown(out) );

  // Pipeline relations (hold regardless of ASYNC/BYPASS)
  assert property ( disable iff (!out_resetn) (cdc_sync_stage1 == $past(in)) );
  assert property ( disable iff (!out_resetn) (cdc_sync_stage2 == $past(cdc_sync_stage1)) );

  // Output mapping per mode
  if (ASYNC_CLK) begin
    assert property ( disable iff (!out_resetn) (out == cdc_sync_stage2) );
  end else begin
    // Bypass mode: out follows in on every sample
    assert property ( out == in );
  end

  // Minimal propagation coverage per bit
  genvar i;
  generate
    if (ASYNC_CLK) begin
      for (i = 0; i < NUM_OF_BITS; i++) begin : COV_ASYNC
        cover property ( disable iff (!out_resetn) $rose(in[i]) ##1 cdc_sync_stage1[i] ##1 out[i] );
        cover property ( disable iff (!out_resetn) $fell(in[i]) ##1 !cdc_sync_stage1[i] ##1 !out[i] );
      end
    end else begin
      for (i = 0; i < NUM_OF_BITS; i++) begin : COV_BYP
        cover property ( $rose(in[i]) && out[i] );
        cover property ( $fell(in[i]) && !out[i] );
      end
    end
  endgenerate

endmodule

// Bind example:
// bind sync_bits sync_bits_sva #(.NUM_OF_BITS(NUM_OF_BITS), .ASYNC_CLK(ASYNC_CLK))
//   u_sync_bits_sva ( .in(in), .out_resetn(out_resetn), .out_clk(out_clk),
//                     .out(out), .cdc_sync_stage1(cdc_sync_stage1), .cdc_sync_stage2(cdc_sync_stage2) );