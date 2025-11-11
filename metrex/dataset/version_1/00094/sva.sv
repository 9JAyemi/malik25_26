// SVA for counter: concise but complete checks and coverage

module counter_sva #(parameter WIDTH=4) (
  input  logic                  clk,
  input  logic                  rst,
  input  logic                  en,
  input  logic                  up,
  input  logic [WIDTH-1:0]      count,
  input  logic [WIDTH-1:0]      count_reg1,
  input  logic [WIDTH-1:0]      count_reg2
);

default clocking cb @(posedge clk); endclocking

// Reset behavior
ap_rst_clears:      assert property (rst |-> (count=='0 && count_reg1=='0 && count_reg2=='0));
ap_rst_holds_zero:  assert property (rst && $past(rst) |-> (count=='0 && count_reg1=='0 && count_reg2=='0));

// Pipeline relations
ap_pipe_cr2:        assert property (disable iff (rst) count_reg2 == $past(count_reg1));
ap_pipe_count:      assert property (disable iff (rst) count      == $past(count_reg2));
ap_pipe_count_2cyc: assert property (disable iff (rst) !$past(rst) && !$past(rst,2) |-> count == $past(count_reg1,2));

// count_reg1 update rules
ap_cr1_inc:         assert property (disable iff (rst) en &&  up |-> count_reg1 == $past(count_reg2) + {{(WIDTH-1){1'b0}},1'b1});
ap_cr1_dec:         assert property (disable iff (rst) en && !up |-> count_reg1 == $past(count_reg2) - {{(WIDTH-1){1'b0}},1'b1});
ap_cr1_hold:        assert property (disable iff (rst) !en       |-> count_reg1 == $past(count_reg1));

// Two-cycle externally visible behavior on count
ap_cnt_inc_2cyc:    assert property (disable iff (rst)
                         !$past(rst,1) && !$past(rst,2) && $past(en,2) &&  $past(up,2)
                         |-> count == $past(count,2) + {{(WIDTH-1){1'b0}},1'b1});
ap_cnt_dec_2cyc:    assert property (disable iff (rst)
                         !$past(rst,1) && !$past(rst,2) && $past(en,2) && !$past(up,2)
                         |-> count == $past(count,2) - {{(WIDTH-1){1'b0}},1'b1});
ap_cnt_hold_2cyc:   assert property (disable iff (rst)
                         !$past(rst,1) && !$past(rst,2) && !$past(en,2)
                         |-> count == $past(count,2));

// No X/Z when not in reset
ap_no_x:            assert property (disable iff (rst) !$isunknown({count,count_reg1,count_reg2,en,up}));

// Coverage: reset, inc/dec, hold, wrap-up/-down observed at output
cv_reset_release:   cover property (rst ##1 !rst);
cv_inc_seen:        cover property (disable iff (rst) $past(en,2) &&  $past(up,2) && count == $past(count,2)+1);
cv_dec_seen:        cover property (disable iff (rst) $past(en,2) && !$past(up,2) && count == $past(count,2)-1);
cv_hold_seen:       cover property (disable iff (rst) !$past(en,2) && count == $past(count,2));
cv_wrap_up:         cover property (disable iff (rst)
                         $past(en,2) &&  $past(up,2) && $past(count,2)=={WIDTH{1'b1}} && count=='0);
cv_wrap_down:       cover property (disable iff (rst)
                         $past(en,2) && !$past(up,2) && $past(count,2)=='0 && count=={WIDTH{1'b1}});

endmodule

// Bind into DUT (connects to ports and internal regs by name)
bind counter counter_sva #(.WIDTH(4)) counter_sva_i (.*);