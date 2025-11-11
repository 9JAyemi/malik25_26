// SVA for four_bit_counter
module four_bit_counter_sva (
  input logic        clk,
  input logic        rst,
  input logic        en,
  input logic [3:0]  count
);
  default clocking cb @(posedge clk); endclocking

  // Basic sanity (no X on control; count known when out of reset)
  a_ctrl_known:   assert property (!$isunknown({rst,en}));
  a_count_known:  assert property (!rst |-> !$isunknown(count));

  // Synchronous reset dominates and holds zero
  a_rst_zero:     assert property (rst |-> (count == 4'h0));

  // Hold when en==0 (avoid first-cycle $past with $past(1'b1) guard)
  a_hold_when_dis: assert property ((!rst && !en && $past(1'b1)) |-> (count == $past(count)));

  // Increment by +1 modulo 16 when en==1
  a_inc_when_en:   assert property ((!rst && en && $past(1'b1)) |-> (count == (($past(count)+4'd1) & 4'hF)));

  // Any change must be due to rst or en
  a_change_has_cause: assert property (($past(1'b1) && (count != $past(count))) |-> (rst || en));

  // Key coverage
  c_reset_effect: cover property (rst |-> (count == 4'h0));
  c_hold:         cover property (!rst && !en && $past(1'b1) && (count == $past(count)));
  c_inc:          cover property (!rst && en && $past(1'b1) && (count == (($past(count)+4'd1) & 4'hF)));
  c_wrap:         cover property (!rst && en && $past(1'b1) && ($past(count)==4'hF) |-> (count==4'h0));
endmodule

// Bind into DUT
bind four_bit_counter four_bit_counter_sva sva (
  .clk(clk),
  .rst(rst),
  .en(en),
  .count(count)
);