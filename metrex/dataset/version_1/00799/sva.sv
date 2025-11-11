// SVA checker for cache_memory_block
module cache_memory_block_sva #(
  parameter int n = 8,
  parameter int m = 16,
  parameter int addr_bits = $clog2(n)
) (
  input logic                 clk,
  input logic                 we,
  input logic                 re,
  input logic [addr_bits-1:0] addr,
  input logic [m-1:0]         wd,
  input logic [m-1:0]         rd
);

  // Sample after NBA to check same-cycle write+read behavior
  default clocking cb @(posedge clk);
    input #1step we, re, addr, wd, rd;
  endclocking

  // Simple shadow model + valid bits
  logic [m-1:0] ref_mem [0:n-1];
  bit           valid   [0:n-1];

  initial begin
    for (int i = 0; i < n; i++) begin
      valid[i] = 1'b0;
      ref_mem[i] = 'x;
    end
  end

  always_ff @(posedge clk) begin
    if (we && !$isunknown({addr, wd})) begin
      ref_mem[addr] <= wd;
      valid[addr]   <= 1'b1;
    end
  end

  // Basic sanity/X checks
  ap_ctrl_known:     assert property (@(posedge clk) !$isunknown({we, re}));
  ap_addr_known_on_access:
                     assert property (@(posedge clk) (we || re) |-> !$isunknown(addr));
  ap_wd_known_on_we: assert property (@(posedge clk) we |-> !$isunknown(wd));

  // Gating: when re==0, rd must be zero
  ap_rd_zero_when_re0:
                     assert property (@cb (!re) |-> (rd == '0));

  // Functional correctness: read returns last written data for that address
  // Covers same-cycle write+read and subsequent reads, gated by valid
  ap_read_correct:   assert property (@cb (re && !$isunknown(addr) && valid[addr]) |-> (rd == ref_mem[addr]));

  // Optional stability: if no write to the addressed location, repeated read is stable
  ap_stable_read:    assert property (@(posedge clk)
                         re && $stable(addr) && !(we && (addr == $past(addr)))
                         |=> rd == $past(rd));

  // Coverage
  cv_we:             cover property (@(posedge clk) we);
  cv_re_valid:       cover property (@cb re && !$isunknown(addr) && valid[addr]);
  cv_same_cycle_raw: cover property (@(posedge clk) we && re);
  cv_raw_next:       cover property (@(posedge clk) we ##1 (re && (addr == $past(addr))));
  cv_re0_zero:       cover property (@cb !re && rd == '0);

endmodule

// Bind into the DUT
bind cache_memory_block cache_memory_block_sva #(.n(n), .m(m)) u_cache_memory_block_sva (.*);