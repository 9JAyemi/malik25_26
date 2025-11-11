// SVA checker for blk_mem_gen
module blk_mem_gen_sva #(parameter WIDTH=8, parameter DEPTH=256)
(
  input logic                   clk,
  input logic [WIDTH-1:0]       din,
  input logic                   we,
  input logic [WIDTH-1:0]       addr,
  input logic [WIDTH-1:0]       dout
);

  default clocking cb @(posedge clk); endclocking

  // Elaboration-time sanity
  initial begin
    assert (DEPTH > 0) else $error("DEPTH must be > 0");
    assert (DEPTH <= (1<<WIDTH)) else $error("DEPTH exceeds addressable range of WIDTH");
  end

  // Basic X/Range checks
  assert property (!$isunknown(we));
  assert property (!$isunknown(addr));
  assert property (we |-> !$isunknown(din));
  assert property ((addr < DEPTH) |-> !$isunknown(dout));
  assert property (we |-> (addr < DEPTH));

  // Combinational read correctness (observed at each clock)
  assert property (1 |-> (dout === mem[addr]));

  // Write correctness (write-first behavior)
  assert property (we && ($past(addr) < DEPTH) |-> ##0 mem[$past(addr)] == $past(din));

  // No spurious memory updates: any change must come from a qualified write to that index
  genvar i;
  generate
    for (i = 0; i < DEPTH; i++) begin : g_no_spurious
      assert property ( (mem[i] != $past(mem[i])) |-> $past(we) && ($past(addr) == i) );
    end
  endgenerate

  // Stability when not writing and address is stable
  assert property (!we && $stable(addr) |-> $stable(dout));

  // Read-during-write same address returns newly written data (write-first)
  assert property (we && (addr == $past(addr)) |-> ##0 dout == $past(din));

  // Coverage
  cover property (we);                               // any write
  cover property (we && addr == '0);                 // write to first address
  cover property (we && addr == (DEPTH-1));          // write to last address
  cover property (we && addr == $past(addr));        // back-to-back write to same address
  cover property (we ##1 (!we && addr == $past(addr) && dout == $past(din))); // write then readback next cycle

endmodule

// Bind into DUT
bind blk_mem_gen blk_mem_gen_sva #(.WIDTH(WIDTH), .DEPTH(DEPTH))
  u_blk_mem_gen_sva (.clk(clk), .din(din), .we(we), .addr(addr), .dout(dout));