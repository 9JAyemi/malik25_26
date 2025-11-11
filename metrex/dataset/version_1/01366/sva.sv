// SVA for counter. Bind this module to the DUT.
module counter_sva (
  input rst, clk, enable,
  input [31:0] inc_value,
  input [31:0] count
);

  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset should drive count to 0 immediately
  ap_async_reset_edge: assert property (@(negedge rst) ##0 (count == 32'd0))
    else $error("count not 0 on async reset edge");

  // While reset is held low, count must stay 0
  ap_reset_level: assert property ( !rst |-> (count == 32'd0) )
    else $error("count not 0 while rst=0");

  // Next-state relation (covers hold, add, and overflow-to-zero) using 33-bit sum
  ap_nextstate: assert property (
    disable iff (!rst)
    1'b1 |=> (
      $past(enable)
        ? ( ({1'b0,$past(count)} + {1'b0,$past(inc_value)})[32]
              ? (count == 32'd0)
              : (count == ({1'b0,$past(count)} + {1'b0,$past(inc_value)})[31:0]) )
        : (count == $past(count))
    )
  ) else $error("Next-state relation violated");

  // If count becomes 0 with enable, it must be due to overflow (no silent clears)
  ap_zero_implies_overflow: assert property (
    disable iff (!rst)
    (count == 32'd0 && $past(enable)) |-> ({1'b0,$past(count)} + {1'b0,$past(inc_value)})[32]
  ) else $error("count cleared without overflow while enable=1");

  // No X/Z on count after reset release
  ap_no_x_on_count: assert property (
    disable iff (!rst) !$isunknown(count)
  ) else $error("count has X/Z");

  // Coverage

  // See a clean async reset event
  cp_reset: cover property (@(negedge rst) 1);

  // See a non-overflowing increment
  cp_add_no_ovf: cover property (
    disable iff (!rst)
    $past(enable) &&
    !(({1'b0,$past(count)} + {1'b0,$past(inc_value)})[32])
    |=> (count == ({1'b0,$past(count)} + {1'b0,$past(inc_value)})[31:0])
  );

  // See an overflow that wraps to zero
  cp_overflow: cover property (
    disable iff (!rst)
    $past(enable) &&
    ({1'b0,$past(count)} + {1'b0,$past(inc_value)})[32]
    |=> (count == 32'd0)
  );

  // See enable asserted with inc_value == 0 (hold under enabled add-by-zero)
  cp_enable_inc0: cover property (
    disable iff (!rst)
    $past(enable) && ($past(inc_value) == 32'd0) |=> (count == $past(count))
  );

  // See hold when enable == 0
  cp_hold: cover property (
    disable iff (!rst)
    !$past(enable) |=> (count == $past(count))
  );

endmodule

// Example bind (place alongside the DUT or in a bind file):
// bind counter counter_sva u_counter_sva (.*);