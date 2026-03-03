// SVA for counter: checks async reset behavior and next-state function; includes key covers.
module counter_sva #(parameter WIDTH=8) (
  input                  clk,
  input                  rst,
  input  [WIDTH-1:0]     max_count,
  input  [WIDTH-1:0]     count
);

  default clocking cb @(posedge clk); endclocking

  // Basic sanity: no X/Z on key signals at clock
  assert property (cb !$isunknown({rst, max_count, count}));

  // Async reset forces count to 0 immediately and holds it while rst=1
  assert property (@(posedge rst) ##0 (count == '0));
  assert property (cb rst |-> ##0 (count == '0));

  // Main next-state function (from previous cycle to this cycle)
  // If rst was asserted last cycle -> count must be 0 now.
  // Else if count==max_count last cycle -> count resets to 0 now.
  // Else -> count increments by 1 now (WIDTH-bit modulo arithmetic).
  assert property (cb disable iff (rst)
    ( $past(rst) ? (count == '0) :
      ( ($past(count) == $past(max_count)) ? (count == '0) :
        (count == $past(count) + {{(WIDTH-1){1'b0}},1'b1}) )
    )
  );

  // Covers
  // See a wrap: reach max_count then go to 0 next cycle
  cover property (cb disable iff (rst)
    ($past(count) == $past(max_count)) ##1 (count == '0)
  );

  // Count up for a few steps (exercise increment path)
  cover property (cb disable iff (rst)
    (count == '0 && max_count >= 3) ##1 (count == 1) ##1 (count == 2) ##1 (count == 3)
  );

  // Corner: max_count==0 holds counter at 0
  cover property (cb disable iff (rst)
    (max_count == '0) ##1 (count == '0) ##1 (count == '0)
  );

  // Corner: max_count dynamic change while counting eventually causes wrap
  cover property (cb disable iff (rst)
    (count > '0 && $changed(max_count)) ##[1:$] ($past(count) == $past(max_count)) ##1 (count == '0)
  );

endmodule

// Bind into DUT
bind counter counter_sva #(.WIDTH(8)) counter_sva_i (.clk(clk), .rst(rst), .max_count(max_count), .count(count));