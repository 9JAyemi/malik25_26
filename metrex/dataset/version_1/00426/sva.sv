// SVA for watchdog_timer
module watchdog_timer_sva #(parameter int timeout = 100)
(
  input logic clk,
  input logic rst,
  input logic wdt,
  input logic [7:0] counter
);

  // Static parameter sanity
  initial assert (timeout >= 0 && timeout <= 8'hFF)
    else $error("watchdog_timer: timeout (%0d) must be 0..255 for 8-bit counter", timeout);

  // Reset drives known values
  assert property (@(posedge clk) rst |-> (counter==8'h00 && wdt==1'b0));

  // Counter increments by 1 modulo-256 when not in reset
  assert property (@(posedge clk) disable iff (rst)
                   $past(!rst) |-> (($past(counter)==8'hFF) ? (counter==8'h00)
                                                           : (counter==$past(counter)+8'd1)));

  // Exact watchdog timing after reset release:
  // stay low for 'timeout' cycles, then rise next cycle
  assert property (@(posedge clk) disable iff (rst)
                   $fell(rst) |-> (!wdt[*timeout]) ##1 $rose(wdt));

  // When counter matches timeout, wdt must assert next cycle
  assert property (@(posedge clk) disable iff (rst)
                   (counter==timeout) |=> wdt);

  // WDT rising edge must be caused by a counter==timeout in the prior cycle
  assert property (@(posedge clk) disable iff (rst)
                   $rose(wdt) |-> ($past(counter)==timeout));

  // WDT can only fall in a cycle where reset is asserted
  assert property (@(posedge clk) $fell(wdt) |-> rst);

  // WDT sticks high while not in reset
  assert property (@(posedge clk) disable iff (rst) wdt |=> wdt);

  // Coverage
  cover property (@(posedge clk) $fell(rst) ##1 (!wdt[*timeout]) ##1 $rose(wdt));
  cover property (@(posedge clk) disable iff (rst) (counter==8'hFF) ##1 (counter==8'h00));
  cover property (@(posedge clk) $rose(wdt));

endmodule

// Bind into DUT
bind watchdog_timer watchdog_timer_sva #(.timeout(timeout))
  watchdog_timer_sva_b (.clk(clk), .rst(rst), .wdt(wdt), .counter(counter));