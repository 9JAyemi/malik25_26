// SVA for async_reset_release
module async_reset_release_sva #(parameter int unsigned DELAY_COUNT = 10)
(
  input logic        clk,
  input logic        rst,
  input logic        enable,
  input logic        rst_release,
  input logic [7:0]  delay_counter
);

  default clocking cb @(posedge clk); endclocking

  // Static parameter check
  initial begin
    assert (DELAY_COUNT <= 8'hFF)
      else $error("async_reset_release: DELAY_COUNT (%0d) exceeds 8-bit counter", DELAY_COUNT);
  end

  // Reset clears state on next cycle
  assert property (cb rst |=> (rst_release == 1'b0 && delay_counter == 8'd0));

  // After leaving reset, state is cleared
  assert property (cb ($past(rst) && !rst) |-> (rst_release == 1'b0 && delay_counter == 8'd0));

  // When disabled (and not in reset), state holds
  assert property (cb disable iff (rst) !enable |=> $stable(delay_counter) && $stable(rst_release));

  // Increment while enabled and below threshold
  assert property (cb disable iff (rst)
                   (enable && (delay_counter < DELAY_COUNT))
                   |=> (delay_counter == $past(delay_counter) + 1) && (rst_release == $past(rst_release)));

  // Saturate counter at DELAY_COUNT (no overflow) and hold there when enabled
  assert property (cb disable iff (rst) delay_counter <= DELAY_COUNT);
  assert property (cb disable iff (rst)
                   (enable && (delay_counter >= DELAY_COUNT))
                   |=> (delay_counter == $past(delay_counter)));

  // No early release before reaching threshold
  assert property (cb disable iff (rst) (delay_counter < DELAY_COUNT) |-> !rst_release);

  // Release asserted one cycle after enable with counter >= threshold
  assert property (cb disable iff (rst)
                   (enable && (delay_counter >= DELAY_COUNT)) |=> rst_release);

  // Release is sticky until reset
  assert property (cb disable iff (rst) rst_release |=> rst_release);

  // The only cause of a rising release is prior enable and counter >= threshold
  assert property (cb disable iff (rst)
                   $rose(rst_release) |-> ($past(enable) && $past(delay_counter >= DELAY_COUNT)));

  // Release may fall only due to reset
  assert property (cb $fell(rst_release) |-> rst);

  // Functional coverage
  cover property (cb
    (!rst && delay_counter == 0 && rst_release == 0)
    ##1 enable[* (DELAY_COUNT+1)]
    ##1 rst_release);

  cover property (cb
    (!rst && delay_counter == 0)
    ##1 enable[* (DELAY_COUNT/2)]
    ##1 !enable[*2]
    ##1 enable[* (DELAY_COUNT+1)]
    ##1 rst_release);

  cover property (cb
    $rose(rst_release) ##1 rst ##1 (!rst && rst_release == 1'b0 && delay_counter == 8'd0));

endmodule

// Bind SVA to DUT
bind async_reset_release
  async_reset_release_sva #(.DELAY_COUNT(delay_count))
  async_reset_release_sva_i (.* , .delay_counter(delay_counter));