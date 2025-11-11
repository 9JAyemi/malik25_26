// SVA for counter
module counter_sva (
  input logic       clk,
  input logic       rst,
  input logic       up_down,
  input logic [1:0] count
);
  default clocking cb @(posedge clk); endclocking

  // Known-ness
  a_rst_known:           assert property ( $past(1'b1) |-> !$isunknown(rst) )
    else $error("counter: rst is X/Z");
  a_known_when_active:   assert property ( $past(1'b1) && !rst |-> !$isunknown({up_down,count}) )
    else $error("counter: up_down/count X/Z when active");

  // Reset behavior (synchronous)
  a_rst_clears:          assert property ( rst |=> count == 2'd0 )
    else $error("counter: reset must clear count to 0 on next cycle");
  a_rst_hold_zero:       assert property ( $past(1'b1) && $past(rst) && rst |-> count == 2'd0 )
    else $error("counter: count must remain 0 while reset is held");

  // Functional step checks (mask both cycles from reset)
  a_inc_step:            assert property ( $past(1'b1) && !rst && !$past(rst) &&  $past(up_down) |-> count == $past(count) + 2'd1 )
    else $error("counter: up step wrong");
  a_dec_step:            assert property ( $past(1'b1) && !rst && !$past(rst) && !$past(up_down) |-> count == $past(count) - 2'd1 )
    else $error("counter: down step wrong");

  // First active cycle after reset deassertion
  a_after_reset_step:    assert property ( $past(1'b1) && $past(rst) && !rst |-> count == (up_down ? 2'd1 : 2'd3) )
    else $error("counter: post-reset first step wrong");

  // Coverage
  c_up_seq:      cover property ( disable iff (rst) count==2'd0 ##1 count==2'd1 ##1 count==2'd2 ##1 count==2'd3 ##1 count==2'd0 );
  c_down_seq:    cover property ( disable iff (rst) count==2'd3 ##1 count==2'd2 ##1 count==2'd1 ##1 count==2'd0 ##1 count==2'd3 );
  c_wrap_up:     cover property ( disable iff (rst) count==2'd3 &&  up_down ##1 count==2'd0 );
  c_wrap_down:   cover property ( disable iff (rst) count==2'd0 && !up_down ##1 count==2'd3 );
  c_post_rst_up:   cover property ( rst ##1 (!rst &&  up_down) ##1 count==2'd1 );
  c_post_rst_down: cover property ( rst ##1 (!rst && !up_down) ##1 count==2'd3 );
endmodule

bind counter counter_sva u_counter_sva(.clk(clk), .rst(rst), .up_down(up_down), .count(count));