// SVA for binary_counter. Bind this to the DUT.
module binary_counter_sva (
  input logic        clk,
  input logic        rst,
  input logic        en,
  input logic        ctrl,
  input logic [3:0]  count
);
  default clocking cb @(posedge clk); endclocking

  // Guard for $past usage (clears across synchronous reset)
  logic past_valid;
  always_ff @(posedge clk) begin
    if (rst) past_valid <= 1'b0;
    else     past_valid <= 1'b1;
  end

  // Output must never go X/Z
  assert property (cb !$isunknown(count)) else $error("count is X/Z");

  // Reset behavior: on any cycle after rst was 1, count must be 0
  assert property (cb past_valid && $past(rst) |-> (count == 4'h0))
    else $error("count not 0 after reset");
  // Also, if rst is 1 now, next cycle must be 0 (belt-and-suspenders)
  assert property (cb rst |=> (count == 4'h0))
    else $error("count not 0 in cycle after rst");

  // Hold when not enabled (no reset in prev cycle)
  assert property (cb disable iff (!past_valid)
                   $past(!rst && !en) |-> (count == $past(count)))
    else $error("count changed while en=0");

  // Increment when enabled and ctrl=0
  assert property (cb disable iff (!past_valid)
                   $past(!rst && en && !ctrl) |-> (count == $past(count) + 4'd1))
    else $error("increment behavior violated");

  // Decrement when enabled and ctrl=1
  assert property (cb disable iff (!past_valid)
                   $past(!rst && en && ctrl) |-> (count == $past(count) - 4'd1))
    else $error("decrement behavior violated");

  // Safety: any change must be driven by either rst or en in the previous cycle
  assert property (cb disable iff (!past_valid)
                   (count != $past(count)) |-> $past(rst || en))
    else $error("count changed without rst or en");

  // Wrap-around checks
  assert property (cb disable iff (!past_valid)
                   $past(!rst && en && !ctrl && $past(count)==4'hF) |-> (count==4'h0))
    else $error("increment wrap 15->0 violated");
  assert property (cb disable iff (!past_valid)
                   $past(!rst && en && ctrl && $past(count)==4'h0) |-> (count==4'hF))
    else $error("decrement wrap 0->15 violated");

  // Coverage
  cover property (cb past_valid && $past(!rst && en && !ctrl) && (count == $past(count)+4'd1)); // inc
  cover property (cb past_valid && $past(!rst && en &&  ctrl) && (count == $past(count)-4'd1)); // dec
  cover property (cb past_valid && $past(!rst && !en) && (count == $past(count)));              // hold
  cover property (cb past_valid && $past(!rst && en && !ctrl && $past(count)==4'hF) && (count==4'h0)); // 15->0
  cover property (cb past_valid && $past(!rst && en &&  ctrl && $past(count)==4'h0) && (count==4'hF)); // 0->15
  cover property (cb $rose(rst));
  cover property (cb $fell(rst));

endmodule

// Bind to the DUT
bind binary_counter binary_counter_sva sva_inst(
  .clk(clk),
  .rst(rst),
  .en(en),
  .ctrl(ctrl),
  .count(count)
);