// SVA for up_counter. Bind this module to the DUT.
module up_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic        enable,
  input logic [2:0]  count
);
  // Sample after NBA updates
  default clocking cb @(posedge clk); endclocking

  // Track past-valid to avoid $past at time 0
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Sanity: no X/Z on key signals
  a_xclean: assert property (!$isunknown({reset, enable, count}));

  // Synchronous reset drives count to zero each cycle reset is asserted
  a_reset_zero: assert property (reset |-> (count == 3'b000));

  // When disabled (and not in/just-after reset), count holds its value
  a_hold_when_disabled: assert property (
    disable iff (!past_valid || reset || $past(reset))
    !enable |=> (count == $past(count))
  );

  // When enabled (and not in/just-after reset), count increments mod-8
  a_inc_when_enabled: assert property (
    disable iff (!past_valid || reset || $past(reset))
    enable |=> (count == (($past(count) == 3'b111) ? 3'b000 : ($past(count) + 3'd1)))
  );

  // Optional: any change (outside reset) must be due to enable
  a_change_requires_enable: assert property (
    disable iff (!past_valid || reset || $past(reset))
    $changed(count) |-> $past(enable)
  );

  // Coverage
  c_seen_reset_zero:  cover property (reset && (count == 3'b000));
  c_hold_cover:       cover property (disable iff (!past_valid || reset || $past(reset))
                                      !enable ##1 (count == $past(count)));
  c_inc_cover:        cover property (disable iff (!past_valid || reset || $past(reset))
                                      (enable && ($past(count) != 3'b111)) ##1 (count == $past(count) + 3'd1));
  c_wrap_cover:       cover property (disable iff (!past_valid || reset || $past(reset))
                                      (enable && ($past(count) == 3'b111)) ##1 (count == 3'b000));

  // Cover that all 8 states are reachable (outside reset)
  generate
    genvar i;
    for (i = 0; i < 8; i++) begin : C_STATES
      cover property (!reset && (count == i[2:0]));
    end
  endgenerate
endmodule

// Bind to DUT
bind up_counter up_counter_sva u_up_counter_sva (.clk(clk), .reset(reset), .enable(enable), .count(count));