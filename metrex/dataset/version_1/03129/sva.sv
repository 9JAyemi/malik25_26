// SVA checker for tiny_memory
module tiny_memory_sva #(parameter int ADDR_W=6, DW=198)
(
  input logic                 clk,
  input logic                 reset,
  input logic                 sel,
  input logic [ADDR_W-1:0]    addr,
  input logic                 w,
  input logic [DW-1:0]        data,
  input logic [DW-1:0]        out,
  input logic                 done
);

default clocking cb @(posedge clk); endclocking
default disable iff (reset);

// Simple shadow model for read-data checking
logic [DW-1:0] shadow_mem [0:(1<<ADDR_W)-1];
bit            valid      [0:(1<<ADDR_W)-1];

integer i;
always_ff @(posedge clk) begin
  if (reset) begin
    for (i=0;i<(1<<ADDR_W);i++) valid[i] <= 1'b0;
  end else if (sel && w) begin
    shadow_mem[addr] <= data;
    valid[addr]      <= 1'b1;
  end
end

// Reset drives outputs low
assert property (@(posedge clk) reset |-> (done==1'b0 && out=='0));

// done mirrors sel when not in reset
assert property (done == sel);

// out only updates on read cycles
assert property (!(sel && !w) |-> $stable(out));

// Read returns last written data for that address (when known)
assert property ((sel && !w && valid[addr]) |-> (out == shadow_mem[addr]));

// Control signals must be known when active
assert property (sel |-> !$isunknown({w, addr}));
assert property (sel && w |-> !$isunknown(data));

// Coverage
cover property (@(posedge clk) reset ##1 !reset);
cover property (sel && w);
cover property (sel && !w);
cover property (sel && w ##1 sel && !w);                  // write then read next cycle
cover property (sel && !w && valid[addr]);                // read of written address
cover property (sel [*3]);                                 // burst of activity
cover property (sel && w && addr=={ADDR_W{1'b0}});         // low address
cover property (sel && w && addr=={ADDR_W{1'b1}});         // high address

endmodule

// Bind to DUT
bind tiny_memory tiny_memory_sva #(.ADDR_W(6), .DW(198)) i_tiny_memory_sva (
  .clk  (clk),
  .reset(reset),
  .sel  (sel),
  .addr (addr),
  .w    (w),
  .data (data),
  .out  (out),
  .done (done)
);