// SVA for module memory. Bind this module to the DUT.
// Focus: address range/known checks, write/read semantics, data integrity, and coverage.

module memory_sva
(
  input logic         clk,
  input logic         wen,
  input logic [31:0]  addr,
  input logic [31:0]  din,
  input logic [31:0]  dout
);

  localparam int ADDR_BITS = 10;

  default clocking cb @(posedge clk); endclocking

  // Guard for $past and |=> on first cycle
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Basic sanity
  assert property (cb !$isunknown({wen, addr, din}));               // no X/Z on inputs
  assert property (cb addr[31:ADDR_BITS] == '0);                    // address in range [0..1023]

  // dout changes only as a result of a read cycle
  assert property (cb past_valid && $changed(dout) |-> $past(!wen));

  // On write cycles, dout must hold its previous value at the next sample
  assert property (cb past_valid && wen |=> dout == $past(dout));

  // One-cycle write-followed-by-read of same address returns written data
  assert property (cb past_valid && $past(wen) && !wen &&
                        (addr[ADDR_BITS-1:0] == $past(addr[ADDR_BITS-1:0]))
                   |-> dout == $past(din));

  // General: A read of address A returns the most recent D written to A,
  // provided no intervening write to A occurred between that write and the read.
  sequence no_write_to_a_between(logic [ADDR_BITS-1:0] a);
    ( !wen || (wen && addr[ADDR_BITS-1:0] != a) )[*0:$];
  endsequence

  property read_returns_last_write_no_intervening;
    automatic logic [ADDR_BITS-1:0] a;
    automatic logic [31:0]          d;
    ( wen, a = addr[ADDR_BITS-1:0], d = din )
    ##1 no_write_to_a_between(a)
    ##1 (!wen && addr[ADDR_BITS-1:0] == a)
    |-> ##1 (dout == d);
  endproperty
  assert property (cb read_returns_last_write_no_intervening);

  // Coverage
  // Basic accesses
  cover property (cb wen);
  cover property (cb !wen);

  // Boundary addresses
  cover property (cb wen && addr[ADDR_BITS-1:0] == '0);
  cover property (cb wen && addr[ADDR_BITS-1:0] == {ADDR_BITS{1'b1}});
  cover property (cb !wen && addr[ADDR_BITS-1:0] == '0);
  cover property (cb !wen && addr[ADDR_BITS-1:0] == {ADDR_BITS{1'b1}});

  // Write followed by read to same address (any distance)
  property wr_then_rd_same_addr;
    automatic logic [ADDR_BITS-1:0] a;
    ( wen, a = addr[ADDR_BITS-1:0] ) ##[1:$] (!wen && addr[ADDR_BITS-1:0] == a);
  endproperty
  cover property (cb wr_then_rd_same_addr);

  // Back-to-back writes to same address
  cover property (cb wen ##1 (wen && addr[ADDR_BITS-1:0] == $past(addr[ADDR_BITS-1:0])));

  // Out-of-range attempt (should not happen per assert; useful to see if stimulus violates)
  cover property (cb addr[31:ADDR_BITS] != '0);

endmodule

// Bind into the DUT
bind memory memory_sva m_sva (.clk(clk), .wen(wen), .addr(addr), .din(din), .dout(dout));