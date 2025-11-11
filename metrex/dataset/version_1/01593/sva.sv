// SVA for counter
module counter_sva(input logic clk, reset, input logic [7:0] count);
  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  a_known:        assert property (!$isunknown({reset,count}));

  // Synchronous reset clears next cycle
  a_reset_clear:  assert property (reset |-> ##1 (count == 8'h00));

  // Properties below are ignored in cycles where reset is 1
  default disable iff (reset);

  // Step behavior: increment or wrap
  a_step: assert property (
    $past(!reset) && !reset |-> (($past(count) != 8'hFF) ? (count == $past(count)+1) : (count == 8'h00))
  );

  // Mod-256 periodicity (no reset during the window)
  a_periodicity:  assert property (1 |-> ##256 (count == $past(count,256)));

  // Coverage
  c_reset_clear:  cover property (reset ##1 (count == 8'h00));
  c_inc:          cover property (!reset && count inside {[8'h00:8'hFE]} ##1 (count == $past(count)+1));
  c_wrap:         cover property (!reset && count == 8'hFF ##1 (count == 8'h00));
  c_reset_to_one: cover property (reset ##1 !reset ##1 (count == 8'h01));
  c_full_cycle:   cover property (!reset && count == 8'h00 ##256 (count == 8'h00));
endmodule

bind counter counter_sva u_counter_sva(.clk(clk), .reset(reset), .count(count));