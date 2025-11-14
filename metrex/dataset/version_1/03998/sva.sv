// SVA for binary_counter
module binary_counter_sva #(parameter W=16) (
  input logic               clk,
  input logic               rst,
  input logic [W-1:0]       max_count,
  input logic [W-1:0]       count
);

  default clocking cb @(posedge clk); endclocking

  // No X/Z on key signals
  a_knowns:          assert property ( !$isunknown({rst, max_count, count}) );

  // Synchronous reset: next cycle is zero; while held, stays zero
  a_reset_next0:     assert property ( rst |=> count == '0 );
  a_reset_hold0:     assert property ( $past(rst) && rst |-> count == '0 );

  // Functional next-state: wrap on equality; increment otherwise (mod W)
  a_wrap_on_equal:   assert property ( !rst && (count == max_count) |=> count == '0 );
  a_inc_otherwise:   assert property ( !rst && (count != max_count) |=> count == $past(count) + 1'b1 );

  // Post-reset release step uses current max_count
  a_post_rst_step:   assert property ( ($past(rst) && !rst) |=> count == ( ($past(max_count) == '0) ? '0 : ($past(count) + 1'b1) ) );

  // ----------------
  // Coverage
  // ----------------
  c_wrap_equal:      cover  property ( !rst && (count == max_count) |=> count == '0 );
  c_increment:       cover  property ( !rst && (count != max_count) |=> count == $past(count) + 1'b1 );
  c_overflow_wrap:   cover  property ( !rst && (count == {W{1'b1}}) && (max_count != {W{1'b1}}) |=> count == '0 );
  c_max0_sticky0:    cover  property ( (!rst && max_count == '0 && count == '0) [*3] );

endmodule

bind binary_counter binary_counter_sva #(.W(16))) u_binary_counter_sva (
  .clk(clk),
  .rst(rst),
  .max_count(max_count),
  .count(count)
);