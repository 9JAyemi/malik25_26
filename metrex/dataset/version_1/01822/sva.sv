// SVA for jserialadder
// Concise checks of reset, counter, full-adder function, shifter, valid-done, and final carry exposure.
// Includes key coverpoints.

module jserialadder_sva (
  input  logic        clk, rst,
  input  logic [3:0]  y,
  input  logic        carryout, isValid,
  input  logic        currentsum, currentcarryout,
  input  logic [1:0]  currentbitcount,
  input  logic        a, b, carryin
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset behavior (also holds during rst high)
  assert property (@cb rst |-> y==4'b0 && carryout==1'b0 && currentbitcount==2'b00 && isValid==1'b0);
  assert property (@cb rst |=> y==4'b0 && carryout==1'b0 && currentbitcount==2'b00 && isValid==1'b0);

  // 2-bit counter increments by 1 modulo-4 each cycle out of reset
  assert property (@cb currentbitcount == $past(currentbitcount) + 2'd1);

  // isValid is a one-cycle pulse when previous count was 3
  assert property (@cb isValid == ($past(currentbitcount) == 2'd3));
  assert property (@cb isValid |=> !isValid);

  // Full-adder function (using previous-cycle inputs)
  // selected carry-in = carryin on first bit (count==0), else previous carryout
  assert property (@cb
    currentsum == ($past(a) ^ $past(b) ^
                  (($past(currentbitcount)==3'd0) ? $past(carryin) : $past(currentcarryout)))
  );
  assert property (@cb
    currentcarryout ==
      (($past(a) & $past(b)) |
       ($past(a) & ( ($past(currentbitcount)==3'd0) ? $past(carryin) : $past(currentcarryout) )) |
       ($past(b) & ( ($past(currentbitcount)==3'd0) ? $past(carryin) : $past(currentcarryout) )))
  );

  // Shift register behavior (uses previous-cycle currentsum and y[3:1])
  assert property (@cb y == { $past(currentsum), $past(y[3:1]) });

  // Completion should expose final carry on the same cycle isValid is asserted
  // (This will FAIL with the current DUT because carryout is gated by an unreachable count==4)
  assert property (@cb isValid |-> carryout == $past(currentcarryout));

  // Simple sanity: carryout is zero before completion
  assert property (@cb !isValid |-> carryout == 1'b0);

  // -----------------
  // Coverage
  // -----------------
  // Observe periodic completion pulse
  cover property (@cb isValid);

  // Exercise both adder carry paths (first-bit vs subsequent-bit)
  cover property (@cb $past(currentbitcount)==2'd0 && currentsum == ($past(a)^$past(b)^$past(carryin)));
  cover property (@cb $past(currentbitcount)!=2'd0 && currentsum == ($past(a)^$past(b)^$past(currentcarryout)));

  // See both values on currentcarryout
  cover property (@cb currentcarryout==1'b0);
  cover property (@cb currentcarryout==1'b1);

  // Try to see carryout asserted (should remain uncovered with current DUT)
  cover property (@cb carryout==1'b1);

  // See a non-zero accumulated sum at a completion point
  cover property (@cb isValid && y!=4'b0000);

endmodule

// Bind example:
// bind jserialadder jserialadder_sva sva (.*);