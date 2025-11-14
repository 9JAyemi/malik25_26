// SVA for watchdog_timer
module watchdog_timer_sva #(parameter int WIDTH = 32) (
  input  logic                  clk,
  input  logic                  rst,
  input  logic [WIDTH-1:0]      timeout,
  input  logic                  wdt,
  input  logic [WIDTH-1:0]      counter
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  localparam logic [WIDTH-1:0] ONE = 'd1;

  // Reset behavior (check even while reset is asserted)
  assert property (@(posedge clk) rst |-> (counter=='0 && wdt==1'b0));

  // No Xs on key signals (outside reset)
  assert property (!$isunknown(counter));
  assert property (!$isunknown(wdt));

  // Counter increments by 1 each cycle (mod 2^WIDTH)
  assert property (counter == $past(counter) + ONE);

  // Exact wdt generation rule (uses old counter, current timeout)
  assert property (wdt == ($past(counter) == timeout));

  // wdt is a single-cycle pulse
  assert property ($rose(wdt) |-> ##1 !wdt);

  // Optional: wdt cannot rise when reset is asserted
  assert property (!rst or !$rose(wdt));

  // Coverage
  cover property ($rose(wdt));                                   // any pulse
  cover property (counter == {WIDTH{1'b1}} ##1 counter == '0);   // wrap-around
  cover property ($fell(rst) ##1 (timeout=='0 && wdt));          // immediate pulse when timeout==0
  cover property ($fell(rst) ##1 (timeout!='0) ##[1:$] $rose(wdt)); // non-zero timeout pulse
endmodule

// Bind to DUT (accesses internal counter)
bind watchdog_timer watchdog_timer_sva #(.WIDTH(32)) u_wdt_sva (
  .clk(clk),
  .rst(rst),
  .timeout(timeout),
  .wdt(wdt),
  .counter(counter)
);