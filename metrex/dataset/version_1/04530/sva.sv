// SVA checker for RAM_SP_AR: single-port RAM with async read, sync write
// Focus: data coherence, async read behavior, X-propagation, and concise coverage

module RAM_SP_AR_sva #(
  parameter int DATA_WIDTH = 8,
  parameter int ADDR_WIDTH = 8,
  localparam int RAM_DEPTH = 1 << ADDR_WIDTH
)(
  input  logic                      clk,
  input  logic [ADDR_WIDTH-1:0]     addr,
  input  logic                      we,
  input  logic [DATA_WIDTH-1:0]     din,
  input  logic [DATA_WIDTH-1:0]     dout
);

  // Shadow model and written-map
  logic [DATA_WIDTH-1:0] mirror [0:RAM_DEPTH-1];
  bit                    written[0:RAM_DEPTH-1];

  // Update mirror on write in the same scheduling region as DUT (posedge)
  always_ff @(posedge clk) begin
    if (we && !$isunknown(addr) && !$isunknown(din)) begin
      mirror[addr]  <= din;
      written[addr] <= 1'b1;
    end
  end

  // Basic X-sanitization on controls
  ap_no_x_ctrl:        assert property (@(posedge clk) !$isunknown(we) && !$isunknown(addr))
                       else $error("X/Z on we or addr");
  ap_no_x_din_on_we:   assert property (@(posedge clk) we |-> !$isunknown(din))
                       else $error("X/Z on din when we=1");

  // Async read must match model for any previously written address
  ap_read_matches_model: assert property (@(addr or posedge clk))
                           (!$isunknown(addr) && written[addr]) |-> ##0 (! $isunknown(dout) && dout == mirror[addr])
                         else $error("dout mismatch for known address");

  // Same-cycle write-through: after the clock edge, dout reflects din (addr stable)
  ap_write_through:    assert property (@(posedge clk)
                           we && $stable(addr) && !$isunknown(din) |-> ##0 (dout == din))
                       else $error("No write-through on same-cycle write");

  // Post-write consistency: after a write, dout equals model at current addr
  ap_post_write_consistency: assert property (@(posedge clk)
                                   we |=> (! $isunknown(dout) && dout == mirror[addr]))
                              else $error("Post-write dout not consistent with model");

  // dout must never be X when addressing a written location
  ap_no_x_dout_on_written: assert property (@(addr or posedge clk))
                              (!$isunknown(addr) && written[addr]) |-> ##0 (! $isunknown(dout))
                            else $error("X/Z on dout for written address");

  // Minimal, meaningful coverage
  cv_any_write:              cover property (@(posedge clk) we);
  cv_write_through:          cover property (@(posedge clk) we && $stable(addr) ##0 (dout == din));
  cv_write_then_read_1cyc:   cover property (@(posedge clk)
                                 we ##1 (!we && addr == $past(addr) && dout == $past(din)));

endmodule

// Bind into DUT
bind RAM_SP_AR RAM_SP_AR_sva #(
  .DATA_WIDTH(DATA_WIDTH),
  .ADDR_WIDTH(ADDR_WIDTH)
) u_ram_sp_ar_sva (
  .clk (clk),
  .addr(addr),
  .we  (we),
  .din (din),
  .dout(dout)
);