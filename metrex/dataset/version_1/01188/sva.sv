// SVA checker for single_port_ram
// Bind this to the DUT; focuses on synchronous read-old-data semantics and address safety.

bind single_port_ram single_port_ram_sva #(
  .addr_width(addr_width),
  .data_width(data_width),
  .mem_depth (mem_depth)
) u_single_port_ram_sva (
  .clock(clock),
  .addr (addr),
  .data (data),
  .we   (we),
  .out  (out)
);

module single_port_ram_sva #(
  parameter addr_width = 8,
  parameter data_width = 8,
  parameter mem_depth  = 1024
)(
  input                      clock,
  input  [addr_width-1:0]    addr,
  input  [data_width-1:0]    data,
  input                      we,
  input  [data_width-1:0]    out
);

  // Shadow model of memory + valid bits
  logic [data_width-1:0] model_mem [0:mem_depth-1];
  bit                    valid     [0:mem_depth-1];

  initial begin
    for (int i = 0; i < mem_depth; i++) begin
      valid[i] = 0;
      model_mem[i] = 'x;
    end
  end

  // Update shadow model exactly like DUT (guarded by range)
  always_ff @(posedge clock) begin
    if (we && (addr < mem_depth)) begin
      model_mem[addr] <= data;
      valid[addr]     <= 1'b1;
    end
  end

  // 1) Address must always be in range
  assert property (@(posedge clock) addr < mem_depth)
    else $error("single_port_ram: addr out of range");

  // 2) No Xs on control/address (optional but recommended)
  assert property (@(posedge clock) !$isunknown(we) && !$isunknown(addr))
    else $error("single_port_ram: X/Z on we/addr");

  // 3) Synchronous read returns OLD data at CURRENT address (read-before-write semantics)
  // out(t) must equal model_mem(addr(t)) sampled at t-1, if that location was previously written.
  property p_sync_read_old_data;
    logic [addr_width-1:0] A;
    @(posedge clock)
      (1, A = addr)
      |->
      (!$past(valid[A])) || (!$isunknown(out) && out == $past(model_mem[A]));
  endproperty
  assert property (p_sync_read_old_data)
    else $error("single_port_ram: out not equal to old data at current address");

  // 4) Next-cycle readback after a write (sanity functional check)
  // If we write to A with D, then on the next cycle if we read A (and do not write a different A),
  // out must be D.
  property p_next_cycle_readback;
    logic [addr_width-1:0] A;
    logic [data_width-1:0] D;
    @(posedge clock)
      (we && (addr < mem_depth), A = addr, D = data)
      ##1 (!we && addr == A) |-> (out == D);
  endproperty
  assert property (p_next_cycle_readback)
    else $error("single_port_ram: next-cycle readback mismatch");

  // 5) When writing and reading same address in the same cycle, out must still be OLD value
  // (explicit version of 3 for WE=1 to catch accidental write-first behavior)
  property p_same_cycle_write_read_old;
    logic [addr_width-1:0] A;
    @(posedge clock)
      (we && (addr < mem_depth), A = addr)
      |->
      (!$past(valid[A])) || (out == $past(model_mem[A]));
  endproperty
  assert property (p_same_cycle_write_read_old)
    else $error("single_port_ram: same-cycle write/read not old-data");

  // Coverage
  // a) First/last address written
  cover property (@(posedge clock) we && addr == '0);
  cover property (@(posedge clock) we && addr == mem_depth-1);
  // b) Back-to-back writes to same address
  cover property (@(posedge clock) (we, $past(we) && addr == $past(addr)));
  // c) Write followed by next-cycle readback of same address
  cover property (p_next_cycle_readback);

endmodule