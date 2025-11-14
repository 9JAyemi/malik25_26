// SVA checker for spram_interface
module spram_interface_sva (
  input logic        clk,
  input logic        WE,
  input logic [7:0]  addr,
  input logic [15:0] wdata,
  input logic [15:0] rdata
);
  default clocking cb @(posedge clk); endclocking

  // Start flag to guard $past usage
  logic started;
  initial started = 0;
  always_ff @(posedge clk) started <= 1;

  // Lightweight reference model to check behavior
  logic [15:0] m [0:255];
  logic [15:0] exp_rdata;

  // Initialize known locations to match DUT
  initial begin
    m[0]  = 16'h1234; m[1]  = 16'h5678; m[2]  = 16'habcd; m[3]  = 16'h0000;
    m[4]  = 16'hffff; m[5]  = 16'hffff; m[6]  = 16'hffff; m[7]  = 16'hffff;
    m[8]  = 16'h0000; m[9]  = 16'h0000; m[10] = 16'h0000; m[11] = 16'h0000;
    m[12] = 16'h0123; m[13] = 16'h4567; m[14] = 16'h89ab; m[15] = 16'hcdef;
  end

  // Mirror DUT timing: read-before-write in same cycle
  always_ff @(posedge clk) begin
    if (WE) m[addr] <= wdata;
    exp_rdata <= m[addr];
  end

  // Core functional check: rdata must match reference model
  assert property (started |-> rdata == exp_rdata)
    else $error("rdata mismatch vs reference model");

  // Write latency: same-address next-cycle read returns the just-written data
  assert property (started && $past(WE) && $stable(addr) |-> rdata == $past(wdata))
    else $error("Write latency to rdata violated");

  // Hold behavior: if addr stable and no write to that addr last cycle, rdata holds
  assert property (started && $stable(addr) && !$past(WE && ($past(addr) == addr)) |-> rdata == $past(rdata))
    else $error("rdata changed without a write to its address");

  // 2-state input checks
  assert property (!$isunknown({WE, addr})))
    else $error("Unknown on WE/addr");
  assert property (WE |-> !$isunknown(wdata))
    else $error("Unknown on wdata during write");

  // rdata is known on the cycle after a write to the selected address
  assert property (started && $past(WE) && $stable(addr) |-> !$isunknown(rdata))
    else $error("rdata unknown after write to same address");

  // Coverage
  cover property ($past(WE) && $stable(addr) && rdata == $past(wdata));            // write -> read same addr next cycle
  cover property (WE && $stable(addr));                                            // read-during-write same addr (old data seen)
  cover property (WE ##1 WE && $past(addr) == addr);                               // back-to-back writes to same addr
  cover property (WE ##1 (WE && addr != $past(addr)));                             // back-to-back writes to different addrs
  cover property (!WE && $changed(addr));                                          // read with address change
  cover property (started && addr == 8'd0  && rdata == 16'h1234);                  // initial content observed (addr 0)
  cover property (started && addr == 8'd1  && rdata == 16'h5678);
  cover property (started && addr == 8'd2  && rdata == 16'habcd);
  cover property (started && addr == 8'd15 && rdata == 16'hcdef);

endmodule

// Bind into DUT
bind spram_interface spram_interface_sva i_spram_interface_sva (
  .clk  (clk),
  .WE   (WE),
  .addr (addr),
  .wdata(wdata),
  .rdata(rdata)
);