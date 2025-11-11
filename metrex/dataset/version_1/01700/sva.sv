// Add this SVA block inside module wptr_full (near the end), or guard with `ifndef SYNTHESIS
// Focused, high-quality checks with concise coverage.

`ifndef SYNTHESIS
// ---------- SVA for wptr_full ----------
localparam int W = ADDRSIZE+1;

default clocking cb @(posedge wclk); endclocking
default disable iff (!wrst_n)

// Reset behavior
assert property (!wrst_n |-> (wfull==0 && awfull==0 && wbin=='0 && wptr=='0));

// Registered next-state updates
assert property ({wbin,wptr} == $past({wbinnext,wgraynext}));

// Gray-code correctness for current wbin/wptr
assert property (wptr == ((wbin>>1) ^ wbin));

// Address mapping
assert property (waddr == wbin[ADDRSIZE-1:0]);

// Increment/stay behavior for binary pointer
assert property ( $past(winc && !wfull) |-> (wbin == $past(wbin)+1) );
assert property ( !$past(winc && !wfull) |-> (wbin == $past(wbin)   ) );

// Gray step (one-bit toggle) when incrementing; no change otherwise
assert property ( $past(winc && !wfull) |-> $onehot(wptr ^ $past(wptr)) );
assert property ( !$past(winc && !wfull) |-> (wptr == $past(wptr)) );

// Full/Almost-full registered from their look-ahead values (pipeline check)
assert property ( wfull  == $past(wfull_val)  );
assert property ( awfull == $past(awfull_val) );

// No X/Z after reset released
assert property ( !$isunknown({wbin,wptr,wfull,awfull,waddr}) );

// ---------- Coverage ----------
cover property ( $rose(wrst_n) ##[1:$] (winc && !wfull) ##[1:$] wfull );    // hit full
cover property ( $rose(wrst_n) ##[1:$] awfull );                             // hit almost-full
cover property ( $past(winc && !wfull) && ($past(wbin)=={W{1'b1}}) && (wbin=='0) ); // wrap
cover property ( wfull ##[1:$] !wfull );                                     // full -> not full
`endif