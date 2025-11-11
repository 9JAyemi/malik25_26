// SVA for binary_display
// Bindable checker focusing on concise, high-value properties

module binary_display_sva(
  input logic        clk,
  input logic [3:0]  data,
  input logic [3:0]  prev_data,
  input logic [3:0]  data_count,
  input logic        display_enable,
  input logic [3:0]  count
);

  default clocking cb @(posedge clk); endclocking

  bit past_valid; initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // prev_data always latches prior data
  assert property (prev_data == $past(data));

  // data_count range and update behavior
  assert property (data_count <= 9);
  assert property ($past(data_count) == 9 |-> data_count == 0);
  assert property (($past(data) == $past(prev_data)) && ($past(data_count) != 9)
                    |-> data_count == $past(data_count) + 1);
  assert property (($past(data) != $past(prev_data)) |-> data_count == 0);

  // display_enable is a 1-cycle pulse asserted iff prior data_count was 9
  assert property (display_enable == ($past(data_count) == 9));
  assert property (display_enable |-> ##1 !display_enable);

  // count update uses previous cycle's display_enable
  assert property ($past(display_enable)
                    |-> count == (($past(count) == 10) ? 0 : $past(count) + 1));
  assert property (!$past(display_enable) |-> count == 0);

  // Stronger invariant given one-cycle enable: count never exceeds 1
  assert property (count inside {[0:1]});

  // High-value coverage
  sequence same_as_prev; data == $past(data); endsequence

  // 10 consecutive same-as-previous cycles produce the pulse
  cover property (same_as_prev[*10] |-> display_enable);

  // Pulse coincident with data change (after 9 consecutive matches)
  cover property (display_enable && (data != $past(data)));

  // Count increments on the cycle after the pulse
  cover property ($past(display_enable) ##1 (count == 1));

endmodule

// Bind to the DUT (connect internal regs as well)
bind binary_display binary_display_sva
  bdsva (
    .clk            (clk),
    .data           (data),
    .prev_data      (prev_data),
    .data_count     (data_count),
    .display_enable (display_enable),
    .count          (count)
  );