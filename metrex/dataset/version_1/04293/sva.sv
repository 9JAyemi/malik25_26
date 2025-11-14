// SVA for ad_rst: reset synchronizer checks and coverage
module ad_rst_sva (
  input  logic clk,
  input  logic rst_async,
  input  logic rst, rstn,
  input  logic rst_async_d1, rst_async_d2,
  input  logic rst_sync, rst_sync_d
);
  default clocking cb @(posedge clk); endclocking

  // Basic relations
  assert property (rstn == ~rst);
  assert property (@(negedge clk) $stable(rst) && $stable(rstn)); // no glitches between clocks
  assert property (cb !$isunknown({rst,rstn}));                   // outputs never X/Z on clock

  // Async assertion behavior
  assert property (@(posedge rst_async) 1 |=> (rst_async_d1 && rst_async_d2 && rst_sync)); // immediate
  assert property (rst_async |-> (rst_async_d1 && rst_async_d2 && rst_sync));              // hold while high

  // Internal 3FF deassertion pattern after rst_async falls
  assert property ($fell(rst_async) |-> 
                   (rst_async_d1==0 && rst_async_d2==1 && rst_sync==1) ##1
                   (rst_async_d1==0 && rst_async_d2==0 && rst_sync==1) ##1
                   (rst_async_d1==0 && rst_async_d2==0 && rst_sync==0));

  // Output rst timing vs rst_async
  assert property ($rose(rst_async) |-> !rst ##1 rst);            // rst asserts 2 cycles after async rise
  assert property ($fell(rst_async) |-> rst[*4] ##1 !rst);        // rst deasserts on 5th cycle after async fall
  assert property (rst_async |-> rst);                            // rst remains asserted while async high

  // Minimum pulse width guarantees (robustness against glitches)
  assert property ($rose(rst) |->  $past(rst_async,1) && $past(rst_async,2));
  assert property ($fell(rst) |-> !$past(rst_async,1) && !$past(rst_async,2) &&
                                   !$past(rst_async,3) && !$past(rst_async,4) && !$past(rst_async,5));

  // Pipeline relation check
  assert property (rst == $past(rst_sync_d));

  // Coverage
  cover property ($rose(rst_async) ##2 rst);
  cover property ($fell(rst_async) ##5 !rst);
  cover property (@(posedge rst_async) rst_async_d1 && rst_async_d2 && rst_sync);
endmodule

// Bind into DUT (connects to internal regs)
bind ad_rst ad_rst_sva u_ad_rst_sva (
  .clk(clk),
  .rst_async(rst_async),
  .rst(rst),
  .rstn(rstn),
  .rst_async_d1(rst_async_d1),
  .rst_async_d2(rst_async_d2),
  .rst_sync(rst_sync),
  .rst_sync_d(rst_sync_d)
);