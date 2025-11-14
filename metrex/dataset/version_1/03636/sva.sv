// SVA for counter. Bind this to the DUT.
module counter_sva(input logic clk, input logic rst, input logic [3:0] count);

  localparam logic [3:0] MAX = 4'd15;

  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  a_known_count:    assert property ( !$isunknown(count) );

  // Reset semantics
  a_reset_zero:     assert property ( rst |-> (count == 4'd0) );
  a_reset_stable:   assert property ( rst && $past(rst) |-> $stable(count) );
  a_post_deassert:  assert property ( $fell(rst) |-> (count == 4'd1) );

  // Counting behavior (only when not in or coming from reset)
  a_inc:  assert property ( !rst && !$past(rst) && ($past(count) != MAX) |-> (count == $past(count) + 4'd1) );
  a_wrap: assert property ( !rst && !$past(rst) && ($past(count) == MAX) |-> (count == 4'd0) );

  // Coverage
  // Hit every value at least once out of reset
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : C_VAL
      c_val: cover property ( !rst && (count == logic'(i[3:0])) );
    end
  endgenerate

  // See a wrap (15 -> 0) with no reset interference
  c_wrap: cover property ( !rst && !$past(rst) && ($past(count) == MAX) && (count == 4'd0) );

  // See a normal increment
  c_inc:  cover property ( !rst && !$past(rst) && ($past(count) != MAX) && (count == $past(count) + 4'd1) );

  // See reset assert/deassert
  c_rst_assert:   cover property ( $rose(rst) );
  c_rst_deassert: cover property ( $fell(rst) );

endmodule

// Bind to DUT
bind counter counter_sva u_counter_sva(.clk(clk), .rst(rst), .count(count));