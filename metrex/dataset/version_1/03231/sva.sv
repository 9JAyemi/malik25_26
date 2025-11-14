// SVA for binary_counter
module binary_counter_sva (
  input logic       clk,
  input logic       rst,
  input logic       en,
  input logic [3:0] count
);

  default clocking @(posedge clk); endclocking
  default disable iff (rst)

  // No X/Z on critical signals (always active)
  assert property (disable iff (1'b0) !$isunknown({rst,en,count}));

  // Synchronous reset drives count to 0 (same cycle)
  assert property (disable iff (1'b0) rst |-> (count == 4'h0));

  // Hold when disabled
  assert property (!en |-> $stable(count));

  // Increment when enabled and not at max
  property p_inc;
    bit [3:0] c;
    (en && (c = count) && (c != 4'hf)) |=> (count == c + 4'd1);
  endproperty
  assert property (p_inc);

  // Wrap from max to zero when enabled
  property p_wrap;
    (en && (count == 4'hf)) |=> (count == 4'h0);
  endproperty
  assert property (p_wrap);

  // Any change must be due to rst or en
  assert property (disable iff (1'b0) $changed(count) |-> (rst || en));

  // Coverage
  sequence s_inc_one; bit [3:0] c; (en && (c = count) && (c != 4'hf)) ##1 (count == c + 4'd1); endsequence
  sequence s_wrap;                 (en && count == 4'hf)               ##1 (count == 4'h0);     endsequence
  sequence s_hold;                 (!en)                                ##1 $stable(count);       endsequence

  cover property (disable iff (1'b0) rst ##1 (count == 4'h0));
  cover property (s_inc_one);
  cover property (s_wrap);
  cover property (s_hold);

endmodule

// Bind to DUT
bind binary_counter binary_counter_sva sva_i (.clk(clk), .rst(rst), .en(en), .count(count));