// SVA for up_down_counter
module up_down_counter_sva (
  input logic clk,
  input logic reset,
  input logic control,
  input logic [3:0] count
);
  default clocking cb @(posedge clk); endclocking

  // Helpers (mod-16 arithmetic)
  function automatic [3:0] inc4(input logic [3:0] a); inc4 = a + 4'd1; endfunction
  function automatic [3:0] dec4(input logic [3:0] a); dec4 = a - 4'd1; endfunction

  // Sanity/knownness
  assert property (!$isunknown({reset, control}));
  assert property (!reset |-> !$isunknown(count)));

  // Synchronous reset
  assert property (reset |-> count == 4'h0);

  // Next-state correctness (single concise check)
  assert property (disable iff (reset)
                   1'b1 |=> count == (control ? inc4($past(count))
                                              : dec4($past(count))));

  // Must change every active cycle
  assert property (disable iff (reset) 1'b1 |=> count != $past(count));

  // Explicit wrap checks
  assert property (disable iff (reset) (control && $past(count)==4'hF) |=> count==4'h0);
  assert property (disable iff (reset) (!control && $past(count)==4'h0) |=> count==4'hF);

  // Coverage
  cover property (reset);
  cover property (disable iff (reset) control ##1 !control);                 // dir change
  cover property (disable iff (reset) (control && $past(count)==4'hF) |=> count==4'h0); // up-wrap
  cover property (disable iff (reset) (!control && $past(count)==4'h0) |=> count==4'hF); // down-wrap
endmodule

bind up_down_counter up_down_counter_sva sva_i (.*);