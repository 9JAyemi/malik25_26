// SVA for modified_decade_counter
// Bind this module to the DUT
module modified_decade_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic        control,
  input logic [3:0]  count,
  input logic [3:0]  next_count
);
  default clocking cb @(posedge clk); endclocking

  // past-valid guard for $past()
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Basic sanity
  // No X/Z on key IOs after first edge
  a_no_x: assert property (past_valid |-> !$isunknown({reset, control, count}));
  // Count stays within 1..10
  a_range: assert property (past_valid |-> count inside {[4'd1:4'd10]});
  // Synchronous reset drives 1
  a_rst:   assert property (past_valid && $past(reset) |-> count == 4'd1);

  // Next-state of count matches RTL (priority: count==10 -> 1; else control==1 && count==5 -> 1; else +1)
  a_cnt_nxt: assert property (
    past_valid && !$past(reset)
    |-> count ==
        ( ($past(count)==4'd10) ? 4'd1 :
          ($past(control) && $past(count)==4'd5) ? 4'd1 :
          ($past(count) + 4'd1) )
  );

  // next_count computation matches RTL (evaluated in previous cycle)
  a_next_cnt_calc: assert property (
    past_valid && !$past(reset)
    |-> $past(next_count) ==
        ( $past(control)
          ? ( ($past(count)==4'd5)  ? 4'd1  : ($past(count)+4'd1) )
          : ( ($past(count)==4'd10) ? 4'd6  : ($past(count)+4'd1) ) )
  );

  // Coverage
  c_seen_rst:    cover property (past_valid && $past(reset) && count==4'd1);
  c_wrap_10_to1: cover property (past_valid && $past(count)==4'd10 && count==4'd1);
  c_ctl1_special:cover property (past_valid && $past(control) && $past(count)==4'd5 && count==4'd1);
  c_ctl1_inc:    cover property (past_valid && $past(control) && $past(count) inside {[4'd1:4'd4]} && count==$past(count)+4'd1);
  c_ctl0_inc:    cover property (past_valid && !$past(control) && $past(count) inside {[4'd1:4'd9]} && count==$past(count)+4'd1);
  c_hit_6:       cover property (past_valid && count==4'd6);
  c_hit_10:      cover property (past_valid && count==4'd10);
endmodule

// Bind into the DUT; ports match DUT internal names, including next_count
bind modified_decade_counter modified_decade_counter_sva sva_inst (.*);