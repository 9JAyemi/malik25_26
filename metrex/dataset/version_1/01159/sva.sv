// Drop this SVA block inside the module (near the end) or guard with a define.
// Concise properties focusing on control, datapath steps, and end-result correctness.
`ifndef SYNTHESIS
// ------------------------ SVA for nonrestore_div ------------------------
default clocking cb @(posedge clk); endclocking
default disable iff (clr);

localparam int N = NUMERATOR_WIDTH;
localparam int D = DENOMINATOR_WIDTH;

// Golden expression to catch the ternary-precedence bug in rem_iter_sum
logic [D:0] golden_sum;
always_comb golden_sum = rem_iter_shift + (rem_iter[REM_ITER_MSB] ? {1'b0,denom} : denom_neg);

// Reset behavior (asynchronous clear observed by next clk)
assert property ($rose(clr) |=> state==s0 && rdy_out==1'b0 &&
                                 numer==0 && denom==0 && denom_neg==0 &&
                                 quot==0 && rem_iter==0 && rem==0 && count==0);

// FSM transitions
assert property (state==s0 |=> state==s1);
assert property ((state==s1 && count != N-1) |=> state==s1);
assert property ((state==s1 && count == N-1) |=> state==s2);
assert property (state==s2 |=> state==s3);
assert property (state==s3 |=> state==s3); // sticky until reset

// rdy_out semantics and output stability in DONE
assert property (rdy_out == (state==s3));
assert property ($rose(state==s3) |-> (quot_out == $past(quot) && rem_out == $past(rem) && rdy_out));
assert property (state==s3 |=> $stable(quot_out) && $stable(rem_out));

// Datapath step checks in iterate state
assert property (state==s1 |-> rem_iter_sum == golden_sum); // detects precedence bug
assert property (state==s1 |=> rem_iter == $past(rem_iter_sum));
assert property (state==s1 |=> quot[QUOT_MSB:1] == $past(quot_shift[QUOT_MSB:1]));
assert property (state==s1 |=> quot[0] == ~ $past(rem_iter_sum[REM_ITER_MSB]));
assert property (state==s1 |=> count == $past(count) + 1);

// Constants captured in s0 remain constant afterward
assert property ((state inside {s1,s2,s3}) |-> $stable(numer) && $stable(denom) && $stable(denom_neg));
// Two's-complement relationship holds for extended widths
assert property ((state inside {s1,s2,s3}) |-> (denom_neg + {1'b0,denom}) == '0);

// Final result correctness for legal denominator
assert property (state==s3 && denom != '0 |-> (
  $unsigned({{D{1'b0}}, numer}) == $unsigned(rem_out) + $unsigned(denom) * $unsigned(quot_out)
));
assert property (state==s3 && denom != '0 |-> (rem_out < denom));

// Useful special-case correctness
assert property (state==s3 && denom != '0 && numer < denom |-> (quot_out=='0 && rem_out==numer));
assert property (state==s3 && numer=='0 && denom != '0 |-> (quot_out=='0 && rem_out=='0));
assert property (state==s3 && denom == {{(D-1){1'b0}},1'b1} |-> (quot_out==numer && rem_out=='0));

// Minimal functional coverage
cover property (state==s0 ##1 state==s1[*N] ##1 state==s2 ##1 state==s3 && denom!='0); // normal complete op
cover property (state==s0 && denom_in=='0 ##1 state==s3); // zero-denominator case observed
// -----------------------------------------------------------------------
`endif