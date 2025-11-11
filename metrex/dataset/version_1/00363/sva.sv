// SVA for counter
module counter_sva #(parameter int WIDTH=4) (
  input  logic              clk,
  input  logic              rst,   // active-low reset in DUT, but here we check rst==1'b0 means reset active
  input  logic [WIDTH-1:0]  count
);
  default clocking cb @(posedge clk); endclocking
  localparam logic [WIDTH-1:0] ONE  = 'd1;
  localparam logic [WIDTH-1:0] ALL1 = {WIDTH{1'b1}};

  // Basic sanity
  a_rst_known:                 assert property (!$isunknown(rst));
  a_count_known_when_active:   assert property (rst |-> !$isunknown(count));

  // Reset behavior
  a_reset_hold_zero:           assert property (!rst |-> (count == '0));
  a_async_reset_zero:          assert property (@(negedge rst) (count == '0)); // immediate on async assertion

  // Counting behavior (mod-2**WIDTH)
  a_inc_active:                assert property (rst && $past(rst) |-> (count == ($past(count) + ONE)));
  a_inc_after_release:         assert property (rst && !$past(rst) |-> (count == ($past(count) + ONE)));
  a_wrap_explicit:             assert property (rst && $past(rst) && ($past(count) == ALL1) |-> (count == '0));

  // Coverage
  c_saw_reset_assert:          cover  property (@(negedge rst) 1);
  c_saw_reset_release:         cover  property ($rose(rst));
  c_first_inc_after_release:   cover  property (rst && !$past(rst) && (count == ONE));
  c_wrap:                      cover  property (rst && $past(rst) && ($past(count) == ALL1) ##1 (count == '0));
endmodule

// Bind into DUT
bind counter counter_sva #(.WIDTH(4)) counter_sva_i (.clk(clk), .rst(rst), .count(count));