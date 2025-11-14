// SVA for BRAM and its wrappers. Bind once to BRAM; covers all sizes.
module BRAM_sva #(parameter AWIDTH=9, DWIDTH=32)
(
  input logic                clk,
  input logic                rce,
  input logic [AWIDTH-1:0]   ra,
  input logic [DWIDTH-1:0]   rq,
  input logic                wce,
  input logic [AWIDTH-1:0]   wa,
  input logic [DWIDTH-1:0]   wd
);

  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  typedef bit [AWIDTH-1:0] addr_t;
  bit [DWIDTH-1:0] refmem [addr_t];
  bit               write_seen [addr_t];

  // Mirror the DUT's initialization intent (0..AWIDTH-2 => 0; last entry unspecified)
  initial begin
    for (int i = 0; i < AWIDTH-1; i++) begin
      refmem[addr_t'(i)]   = '0;
      write_seen[addr_t'(i)] = 1'b0;
    end
    write_seen[addr_t'(AWIDTH-1)] = 1'b0;
  end

  // Reference model update on write
  always_ff @(posedge clk) begin
    if (wce && !$isunknown({wa,wd})) begin
      refmem[wa]   <= wd;
      write_seen[wa] <= 1'b1;
    end
  end

  // Basic sanity
  a_ctrl_known:              assert property (!$isunknown({rce,wce}));
  a_addr_known_when_read:    assert property (rce |-> !$isunknown(ra));
  a_addr_known_when_write:   assert property (wce |-> !$isunknown({wa,wd}));

  // DUT's actual array is [0:AWIDTH-1]; flag any out-of-range access
  a_read_addr_in_range:      assert property (rce |-> ra < AWIDTH);
  a_write_addr_in_range:     assert property (wce |-> wa < AWIDTH);

  // rq updates only when rce; otherwise holds value
  a_rq_holds_without_rce:    assert property (past_valid && !$past(rce) |-> rq == $past(rq));

  // Synchronous read: data seen is model value from previous cycle
  a_read_matches_model:      assert property (past_valid && rce |-> rq === $past(refmem[ra]));

  // Same-cycle read & write to same addr returns old data (read-before-write)
  a_rw_same_cycle_old_data:  assert property (past_valid && rce && wce && (ra==wa) |-> rq === $past(refmem[ra]));

  // Power-on init intent: addresses 0..AWIDTH-2 read as 0 until first write to them
  a_init_zero_lower_range:   assert property (past_valid && rce && (ra < (AWIDTH-1)) && !write_seen[ra] |-> rq === '0);

  // Coverage
  c_write:                   cover property (wce);
  c_read:                    cover property (rce);
  c_rw_same_cycle:           cover property (rce && wce && (ra==wa));
  c_write_then_read:         cover property (wce ##1 (rce && (ra == $past(wa))));
  c_read_addr0:              cover property (rce && (ra == '0));
  c_last_addr_after_write:   cover property (wce && (wa == (AWIDTH-1)) ##1 (rce && (ra == (AWIDTH-1))));

endmodule

// Bind to all BRAM instances (covers BRAM_32x512, BRAM_16x1024, BRAM_8x2048, BRAM_4x4096)
bind BRAM BRAM_sva #(.AWIDTH(AWIDTH), .DWIDTH(DWIDTH)) i_bram_sva (.*);