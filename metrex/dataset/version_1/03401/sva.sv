// SVA for single_port_ram
// Bind into the DUT; focuses on core behaviors, X-checks, and concise coverage

module single_port_ram_sva #(
  parameter int ADDR_W = 11,
  parameter int DATA_W = 8
)(
  input  logic                  clk,
  input  logic                  en,
  input  logic                  we,
  input  logic [ADDR_W-1:0]     addr,
  input  logic [DATA_W-1:0]     din,
  input  logic [DATA_W-1:0]     dout,
  // Access DUT RAM by reference for precise checks
  ref    logic [DATA_W-1:0]     ram [0:(1<<ADDR_W)-1]
);

  // Past-valid guard to make $past-safe from time 0
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Basic X/Z checks on controls and data when used
  assert property (cb !$isunknown({en,we,addr}));
  assert property (cb (en && we) |-> !$isunknown(din));

  // Write semantics: on write, the addressed location updates with din
  assert property (cb (en && we) |=> ram[$past(addr)] == $past(din));

  // No unintended writes: if not (en && we), the previously addressed location is unchanged
  assert property (cb !(en && we) |=> ram[$past(addr)] == $past(ram[$past(addr)]));

  // Read semantics: on read, dout updates next cycle with the addressed RAM value
  assert property (cb (en && !we) |=> dout == $past(ram[$past(addr)]));

  // dout changes only due to a read cycle
  assert property (cb $changed(dout) |-> $past(en && !we));

  // During a write cycle, dout must not change (no read-while-write)
  assert property (cb (en && we) |=> $stable(dout));

  // Read-after-write to same address returns the just-written data
  assert property (cb (en && we) ##1 (en && !we && addr == $past(addr)) |-> dout == $past(din,1));

  // Concise functional coverage
  cover property (cb en && we);                             // a write occurs
  cover property (cb en && !we);                            // a read occurs
  cover property (cb (en && we) ##1 (en && !we));           // write followed by read
  cover property (cb (en && we) ##1 (en && !we && addr==$past(addr))); // RAW same addr
  cover property (cb (en && we) ##1 (en && we && addr!=$past(addr)));  // back-to-back writes, different addr

endmodule

// Bind into the DUT instance(s)
bind single_port_ram single_port_ram_sva #(.ADDR_W(11), .DATA_W(8)) i_single_port_ram_sva (
  .clk (clk),
  .en  (en),
  .we  (we),
  .addr(addr),
  .din (din),
  .dout(dout),
  .ram (ram)
);