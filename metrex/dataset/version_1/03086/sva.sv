// SVA for logicblock_counter
module logicblock_counter_sva #(parameter DATA_WIDTH=32) (
  input  logic                     clock,
  input  logic                     resetn,
  input  logic                     i_start,
  input  logic [DATA_WIDTH-1:0]    i_size,
  input  logic [DATA_WIDTH-1:0]    o_dataout,
  input  logic                     o_dataout_valid,
  input  logic                     i_dataout_stall,
  input  logic                     i_counter_reset
);

  default clocking cb @(posedge clock); endclocking

  // Handy enables
  let can_count = i_start && !i_counter_reset && (o_dataout < i_size);
  let inc_en    = o_dataout_valid && !i_dataout_stall; // equivalent to can_count && !stall

  // Reset behavior (asynchronous low)
  assert property (!resetn |-> o_dataout == '0);

  // Synchronous counter reset forces zero next cycle and while held
  assert property (disable iff (!resetn) i_counter_reset |=> o_dataout == '0);
  assert property (disable iff (!resetn) $past(i_counter_reset) && i_counter_reset |-> o_dataout == '0);

  // o_dataout_valid definition
  assert property (o_dataout_valid == (i_start && !i_counter_reset && (o_dataout < i_size)));

  // Increment exactly by 1 when enabled
  assert property (disable iff (!resetn) inc_en |=> o_dataout == $past(o_dataout) + 1);

  // Hold value when not incrementing and not resetting
  assert property (disable iff (!resetn) (!i_counter_reset && !inc_en) |=> o_dataout == $past(o_dataout));

  // Monotonic non-decreasing (except during reset)
  assert property (disable iff (!resetn || i_counter_reset) o_dataout >= $past(o_dataout));

  // Valid must be low at/above size
  assert property (disable iff (!resetn) (o_dataout >= i_size) |-> !o_dataout_valid);

  // Clean outputs (no X/Z) after reset released
  assert property (disable iff (!resetn) !$isunknown({o_dataout, o_dataout_valid}));

  // Boundary step: last valid beat drops valid on next cycle if size is stable and non-zero
  assert property (disable iff (!resetn)
                   (i_size != '0) && $stable(i_size) &&
                   (o_dataout == i_size - 1) && can_count && !i_dataout_stall
                   |=> (o_dataout == $past(i_size)) && !o_dataout_valid);

  // Coverage
  cover property (disable iff (!resetn) inc_en [*3]); // 3 consecutive increments
  cover property (disable iff (!resetn) o_dataout_valid && i_dataout_stall ##1 o_dataout_valid && !i_dataout_stall ##1 inc_en);
  cover property (disable iff (!resetn)
                  (i_size != '0) && $stable(i_size) &&
                  (o_dataout == i_size - 1) && can_count && !i_dataout_stall
                  ##1 (o_dataout == $past(i_size)) && !o_dataout_valid);
endmodule