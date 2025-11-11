// Drop this SVA block inside binary_counter or bind it to the instance.
// Focused, high-signal assertions + coverage.

`ifdef SVA
// Default clock and simple past-valid guard (no explicit reset in DUT)
default clocking cb @(posedge clk); endclocking
logic past_valid; initial past_valid = 1'b0; always @(posedge clk) past_valid <= 1'b1;
default disable iff (!past_valid)

// State encoding must always be valid
assert property (current_state inside {IDLE, COUNTING, RESET});

// IDLE transitions are fully determined by rst
assert property ((current_state==IDLE && rst)  |=> current_state==RESET);
assert property ((current_state==IDLE && !rst) |=> current_state==COUNTING);

// RESET behavior: force count=0 and go to IDLE next
assert property ((current_state==RESET) |->  count==3'b000);
assert property ((current_state==RESET) |=> current_state==IDLE);

// COUNTING behavior: count must increment every cycle
assert property ((current_state==COUNTING) |-> count == $past(count)+3'b001);

// COUNTING exit condition (intended): when count hits 7, go to IDLE next and count is 0
// This will flag the RTL bug where 'counter' (not 'count') gates the transition.
assert property ((current_state==COUNTING && count==3'b111) |=> (current_state==IDLE && count==3'b000));

// IDLE must not change count
assert property ((current_state==IDLE) |-> $stable(count));

// Disallow illegal self-loop from IDLE (redundant with the two IDLE assertions above but concise)
assert property ((current_state==IDLE) |=> current_state inside {RESET, COUNTING});

// ------------- Coverage -------------
// See all states
cover property (current_state==IDLE);
cover property (current_state==COUNTING);
cover property (current_state==RESET);

// Take the nominal path into COUNTING
cover property ((current_state==IDLE && !rst) ##1 current_state==COUNTING);

// Hit terminal count and return to IDLE (will not cover with current RTL due to the bug)
cover property ((current_state==COUNTING && count==3'b111) ##1 current_state==IDLE);

// Exercise reset path IDLE->RESET->IDLE
cover property ((current_state==IDLE && rst) ##1 (current_state==RESET) ##1 (current_state==IDLE));
`endif