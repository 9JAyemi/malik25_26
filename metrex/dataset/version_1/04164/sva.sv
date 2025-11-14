// SVA for BRAM_SDP and all its parameterized wrappers
// Concise, high-quality checks with functional scoreboard; bind to BRAM_SDP.

// Assertion module (bind target)
module bram_sdp_sva #(
  parameter AWIDTH = 9,
  parameter DWIDTH = 32
)(
  input  logic                   clk,
  input  logic                   rce,
  input  logic [AWIDTH-1:0]      ra,
  input  logic                   wce,
  input  logic [AWIDTH-1:0]      wa,
  input  logic [DWIDTH-1:0]      wd,
  input  logic [DWIDTH-1:0]      rq
);

  // Basic parameter sanity
  initial begin
    assert (AWIDTH > 0) else $error("AWIDTH must be > 0");
    assert (DWIDTH > 0) else $error("DWIDTH must be > 0");
  end

  // Start gating for $past usage
  bit started;
  always @(posedge clk) started <= 1'b1;

  // 2-state scoreboard model for last written value per address
  typedef bit [AWIDTH-1:0] addr_t;
  typedef bit [DWIDTH-1:0] data_t;
  data_t model[addr_t];

  // Update model only with known inputs
  always @(posedge clk) begin
    if (wce && !$isunknown({wa, wd})) model[wa] <= wd;
  end

  default clocking @(posedge clk); endclocking

  // Inputs must be known when enabled
  assert property (disable iff (!started) rce |-> !$isunknown(ra))
    else $error("Read CE asserted with unknown address");
  assert property (disable iff (!started) wce |-> !$isunknown({wa, wd}))
    else $error("Write CE asserted with unknown address/data");

  // Read data must match model (read-first behavior via $past(model))
  // Only check for addresses that have been written at least once
  assert property (disable iff (!started)
                   rce && model.exists(ra) && !$isunknown(ra)
                   |-> (rq == $past(model[ra])))
    else $error("Read data mismatch vs. model (read-first)");

  // rq updates only when rce is asserted (no spurious changes)
  assert property (disable iff (!started) $changed(rq) |-> rce)
    else $error("rq changed without rce");

  // rq holds when rce deasserted
  assert property (disable iff (!started) !rce |-> (rq == $past(rq)))
    else $error("rq not held when rce=0");

  // Optional: when rce and model exists, rq must be known
  assert property (disable iff (!started)
                   rce && model.exists(ra) && !$isunknown(ra)
                   |-> !$isunknown(rq))
    else $error("rq is unknown on valid modeled read");

  // Coverage: basic ops
  cover property (disable iff (!started) wce && !$isunknown({wa, wd}));                      // write
  cover property (disable iff (!started) rce && !$isunknown(ra));                             // read
  cover property (disable iff (!started) rce && model.exists(ra) && !$isunknown(ra));         // read-hit
  cover property (disable iff (!started) rce && wce && (ra == wa) && !$isunknown({ra, wd}));  // same-cycle R/W same addr
  cover property (disable iff (!started) wce && (wa == '0));
  cover property (disable iff (!started) wce && (wa == {AWIDTH{1'b1}}));
  cover property (disable iff (!started) rce && (ra == '0));
  cover property (disable iff (!started) rce && (ra == {AWIDTH{1'b1}}));

endmodule

// Bind to all BRAM_SDP instances (covers wrappers too)
bind BRAM_SDP bram_sdp_sva #(.AWIDTH(AWIDTH), .DWIDTH(DWIDTH)) u_bram_sdp_sva (
  .clk(clk),
  .rce(rce),
  .ra(ra),
  .wce(wce),
  .wa(wa),
  .wd(wd),
  .rq(rq)
);