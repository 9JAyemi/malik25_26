// SVA for memory_protection_block
module memory_protection_block_sva #(parameter int n = 8) (
  input  logic [n-1:0] addr,
  input  logic         we,
  input  logic         rd,
  input  logic         wr,
  input  logic [n-1:0] protected_addr
);

  // Helper: avoid out-of-range bit-selects into protected_addr
  logic addr_in_range;
  assign addr_in_range = (addr < n);

  // rd must always be 1 and known
  assert property (@(addr or we) rd === 1'b1);

  // No write when !we
  assert property (@(addr or we) !we |-> (wr === 1'b0));

  // Block writes to protected addresses (when index is in range)
  assert property (@(addr or we) we && addr_in_range && protected_addr[addr] |-> (wr === 1'b0));

  // Allow writes to unprotected addresses (when index is in range)
  assert property (@(addr or we) we && addr_in_range && !protected_addr[addr] |-> (wr === 1'b1));

  // Forbid write attempts that would index out of range
  assert property (@(addr or we) we |-> addr_in_range);

  // Outputs never unknown
  assert property (@(addr or we) !$isunknown(rd));
  assert property (@(addr or we) !$isunknown(wr));

  // Functional coverage
  cover property (@(addr or we) !we && wr == 1'b0);
  cover property (@(addr or we) we && addr_in_range && protected_addr[addr]  && wr == 1'b0);
  cover property (@(addr or we) we && addr_in_range && !protected_addr[addr] && wr == 1'b1);

endmodule

// Bind into the DUT
bind memory_protection_block memory_protection_block_sva #(.n(n)) mpb_sva_b (
  .addr(addr),
  .we(we),
  .rd(rd),
  .wr(wr),
  .protected_addr(protected_addr)
)