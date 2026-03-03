// SVA for binary_counter
module binary_counter_sva #(parameter int MAX_COUNT=15)
(
  input logic        clk,
  input logic        reset,
  input logic [3:0]  count,
  input logic        overflow
);

  // Parameter sanity (fits in 4 bits)
  initial begin
    assert (MAX_COUNT inside {[0:15]})
      else $error("MAX_COUNT (%0d) must be in [0..15] for 4-bit counter", MAX_COUNT);
  end

  // Immediate async reset effect
  always @(posedge reset) begin
    assert (count==0 && overflow==0)
      else $error("Async reset must drive count=0, overflow=0 immediately");
  end

  // While reset is asserted, outputs held at 0 on each clk edge
  assert property (@(posedge clk) disable iff(1'b0)
                   reset |-> (count==0 && overflow==0))
    else $error("While reset=1, count/overflow must hold at 0");

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Normal increment when not at MAX_COUNT
  assert property ( $past(!reset) && ($past(count) != MAX_COUNT)
                    |=> (count == $past(count)+1) && (overflow == 1'b0) )
    else $error("Increment path: next count!=prev+1 or overflow!=0");

  // Roll to 0 and assert overflow when at MAX_COUNT
  assert property ( $past(!reset) && ($past(count) == MAX_COUNT)
                    |=> (count == 4'd0) && (overflow == 1'b1) )
    else $error("MAX_COUNT hit: next count must be 0 and overflow=1");

  // Overflow only when previous count was MAX_COUNT
  assert property ( overflow |-> ($past(!reset) && ($past(count) == MAX_COUNT)) )
    else $error("Spurious overflow without prior MAX_COUNT");

  // After an overflow pulse, it deasserts next cycle if MAX_COUNT!=0
  assert property ( (overflow && (MAX_COUNT != 0)) |=> !overflow )
    else $error("Overflow should deassert in 1 cycle when MAX_COUNT!=0");

  // No X/Z on observable outputs during operation
  assert property ( !$isunknown({count,overflow}) )
    else $error("count/overflow contain X/Z");

  // Optional: no overflow on natural 15->0 wrap if MAX_COUNT!=15
  assert property ( (MAX_COUNT != 4'd15) && $past(!reset) && ($past(count)==4'hF)
                    |=> (count==4'd0) && (overflow==1'b0) )
    else $error("Unexpected overflow on 15->0 wrap when MAX_COUNT!=15");

  // Coverage
  cover property ( $past(!reset) && ($past(count) != MAX_COUNT)
                   |=> (count == $past(count)+1) && !overflow ); // increment path

  cover property ( $past(!reset) && ($past(count) == MAX_COUNT)
                   |=> (count == 4'd0) && overflow ); // overflow event

  cover property ( (MAX_COUNT != 4'd15) && $past(!reset) && ($past(count)==4'hF)
                   |=> (count==4'd0) && !overflow ); // wrap w/o overflow

  cover property ( (MAX_COUNT==0) && !reset [*2] ##1 (overflow ##1 overflow) ); // MAX_COUNT==0 sticky overflow

endmodule

// Bind into DUT
bind binary_counter binary_counter_sva #(.MAX_COUNT(MAX_COUNT))
  i_binary_counter_sva (.*);