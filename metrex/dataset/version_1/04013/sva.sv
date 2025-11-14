// Drop this SVA block inside module counter or bind it in

// synopsys translate_off
// pragma translate_off
`ifndef COUNTER_SVA
`define COUNTER_SVA

// Assertions for counter
// Notes:
// - Use 3-arg $past(...,1,default) to avoid first-cycle Xs
// - Default clock: posedge CP

default clocking cb @(posedge CP); endclocking

localparam logic [7:0] ZERO = 8'h00;
localparam logic [7:0] ONES = 8'hFF;

// Q update behavior and priority (CLR_ dominates LD_)
assert property (
  1 |-> ( !$past(CLR_,1,1'b1) ? (Q == ZERO) :
          !$past(LD_ ,1,1'b1) ? (Q == $past(RS,1,ZERO)) :
           $past(M   ,1,1'b1) ? (Q == ($past(Q,1,ZERO) + 8'h01)) :
                                 (Q == ($past(Q,1,ZERO) - 8'h01)) )
);

// TEMP must reflect carry/borrow condition from prior state when enabled
assert property (
  TEMP == (
    ( (!$past(M,1,1'b1) && ($past(Q,1,ZERO) == ZERO)) ||
      ( $past(M,1,1'b1) && ($past(Q,1,ZERO) == ONES)) )
    && $past(CLR_,1,1'b1) && $past(LD_,1,1'b1)
  )
);

// QCC_ is TEMP AND CP (level relationship on both clock edges)
assert property (@(posedge CP) QCC_ == TEMP);
assert property (@(negedge CP) QCC_ == 1'b0);

// Monotonic step when enabled (redundant with Q update but clearer intent)
assert property ( $past(CLR_,1,1'b1) && $past(LD_,1,1'b1) &&  $past(M,1,1'b1)
                  |-> Q == ($past(Q,1,ZERO) + 8'h01) );
assert property ( $past(CLR_,1,1'b1) && $past(LD_,1,1'b1) && !$past(M,1,1'b1)
                  |-> Q == ($past(Q,1,ZERO) - 8'h01) );

// Sanity: no unknowns on Q after a valid update cycle
assert property (
  $past(CLR_,1,1'b1) && $past(LD_,1,1'b1) |-> !$isunknown(Q)
);

// ---------------- Coverage ----------------

// Reset takes effect
cover property ( !$past(CLR_,1,1'b1) ##1 (Q == ZERO) );

// Parallel load takes effect
cover property ( $past(CLR_,1,1'b1) && !$past(LD_,1,1'b1) ##1 (Q == $past(RS,1,ZERO)) );

// Increment wrap (carry) pulse
cover property (
  $past(CLR_,1,1'b1) && $past(LD_,1,1'b1) &&
  $past(M,1,1'b1) && ($past(Q,1,ZERO) == ONES)
  ##1 (TEMP && QCC_ && (Q == ZERO))
);

// Decrement wrap (borrow) pulse
cover property (
  $past(CLR_,1,1'b1) && $past(LD_,1,1'b1) &&
  !$past(M,1,1'b1) && ($past(Q,1,ZERO) == ZERO)
  ##1 (TEMP && QCC_ && (Q == ONES))
);

// A few consecutive increments and decrements (exercise normal paths)
cover property ( $past(CLR_,1,1'b1) && $past(LD_,1,1'b1) && $past(M,1,1'b1) [*3] );
cover property ( $past(CLR_,1,1'b1) && $past(LD_,1,1'b1) && !$past(M,1,1'b1) [*3] );

`endif
// pragma translate_on
// synopsys translate_on