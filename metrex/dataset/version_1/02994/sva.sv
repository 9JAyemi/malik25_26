// SVA checker for counter_4bit
module counter_4bit_sva (
  input  logic       clk,
  input  logic       rst,   // active-low in DUT, but used as-is here
  input  logic       en,
  input  logic [3:0] count
);
  default clocking cb @(posedge clk); endclocking

  // Track when $past() is valid in the active (rst==1) domain
  bit past_valid;
  always @(posedge clk or negedge rst) begin
    if (!rst) past_valid <= 1'b0;
    else      past_valid <= 1'b1;
  end

  // Asynchronous reset: immediate and level behavior
  ap_async_rst_immed: assert property (@(negedge rst) ##0 (count == 4'h0));
  ap_rst_level_zero:  assert property (@(posedge clk) !rst |-> (count == 4'h0));

  // Count must be known at clocks
  ap_count_known:     assert property (@(posedge clk) !$isunknown(count));

  // Next-state function (when out of reset)
  ap_hold_when_dis:   assert property (disable iff (!rst || !past_valid)
                                       !en |-> count == $past(count));
  ap_inc_when_en:     assert property (disable iff (!rst || !past_valid)
                                       en  |-> count == ($past(count) + 4'd1));

  // No spurious changes: a change implies en was 1 in prior cycle
  ap_change_implies_en: assert property (disable iff (!rst || !past_valid)
                                         $changed(count) |-> $past(en));

  // Explicit wrap-around check
  ap_wrap:            assert property (disable iff (!rst || !past_valid)
                                       ($past(count)==4'hF && en) |-> (count==4'h0));

  // Coverage
  cp_reset_then_inc:  cover property (@(posedge clk)
                                      !rst ##1 rst ##1 en ##1 (count==4'd1));
  cp_hold:            cover property (disable iff (!rst || !past_valid)
                                      !en ##1 (!en && count == $past(count)));
  cp_wrap:            cover property (disable iff (!rst || !past_valid)
                                      ($past(count)==4'hF && en) |-> (count==4'h0));
  cp_run_16:          cover property (disable iff (!rst)
                                      (en[*16]) ##0 (count == $past(count,16)));
endmodule

bind counter_4bit counter_4bit_sva u_counter_4bit_sva (.clk(clk), .rst(rst), .en(en), .count(count));