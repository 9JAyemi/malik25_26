// SVA checker for counter
module counter_sva (input logic clk, rst, input logic [3:0] count);

  default clocking cb @(posedge clk); endclocking

  // Track valid past sample to guard $past()
  logic past_valid;
  always @(posedge clk or posedge rst) begin
    if (rst) past_valid <= 1'b0;
    else     past_valid <= 1'b1;
  end

  // 1) Asynchronous reset clears immediately
  assert property (@(posedge rst) count == 4'h0)
    else $error("count not 0 on posedge rst");

  // 2) While reset is asserted, count must be 0 on every clk
  assert property (rst |-> count == 4'h0)
    else $error("count not 0 while rst=1 at clk edge");

  // 3) No X/Z on count at clk or rst edges
  assert property (!$isunknown(count))
    else $error("count has X/Z at clk edge");
  assert property (@(posedge rst) !$isunknown(count))
    else $error("count has X/Z at rst edge");

  // 4) Increment rule when not wrapping
  assert property (past_valid && !rst && !$past(rst) && ($past(count) != 4'hF)
                   |-> count == $past(count) + 4'h1)
    else $error("count did not increment by +1");

  // 5) Wrap rule at 0xF -> 0x0
  assert property (past_valid && !rst && !$past(rst) && ($past(count) == 4'hF)
                   |-> count == 4'h0)
    else $error("count did not wrap 0xF->0x0");

  // 6) Count may only change on a clk or rst rising edge
  assert property ($changed(count) |-> ($rose(clk) or $rose(rst)))
    else $error("count changed without clk or rst edge");

  // Coverage
  cover property (@(posedge rst) count == 4'h0);                          // async clear observed
  cover property (disable iff (rst) past_valid && ($past(count) == 4'hF) && (count == 4'h0)); // wrap observed
  cover property (disable iff (rst) count == 4'h0 ##16 count == 4'h0);    // full 16-count cycle

endmodule

// Bind into DUT
bind counter counter_sva u_counter_sva (.clk(clk), .rst(rst), .count(count));