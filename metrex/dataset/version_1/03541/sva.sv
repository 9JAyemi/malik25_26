// SystemVerilog Assertions for antares_divider
// Place inside the module or bind to the instance.
// Focused, high-value checks: protocol, latency, datapath updates, and final arithmetic correctness.

`ifndef SYNTHESIS
// Helpers
function automatic [31:0] abs32(input [31:0] x);
  abs32 = x[31] ? -x : x;
endfunction

default clocking cb @(posedge clk); endclocking
default disable iff (rst);

// Basic protocol
assert property (!(op_divs && op_divu))
  else $error("DIV: op_divs and op_divu must be mutually exclusive");

assert property (active |-> !op_divs && !op_divu)
  else $error("DIV: New request while active");

// Stall mapping
assert property (div_stall == active)
  else $error("DIV: div_stall must mirror active");

// Start initialization (unsigned)
assert property ( (op_divu && !active) |-> ##1
                  (active && cycle==5'd31 && residual==32'h0 &&
                   result==$past(dividend) && denominator==$past(divisor) &&
                   neg_result==1'b0 && neg_remainder==1'b0) )
  else $error("DIVU: Bad init");

// Start initialization (signed)
assert property ( (op_divs && !active) |-> ##1
                  (active && cycle==5'd31 && residual==32'h0 &&
                   result==abs32($past(dividend)) &&
                   denominator==abs32($past(divisor)) &&
                   neg_result==($past(dividend[31]) ^ $past(divisor[31])) &&
                   neg_remainder==$past(dividend[31])) )
  else $error("DIVS: Bad init");

// Busy length: exactly 32 cycles then idle
sequence start_div; (op_divs || op_divu) && !active; endsequence
assert property ( start_div |-> ##1 active [*32] ##1 !active )
  else $error("DIV: Busy length not 32 cycles");

// Active deassert cause
assert property ( (!active && $past(active)) |-> $past(cycle)==5'd0 )
  else $error("DIV: Deassert without cycle==0");

// Cycle monotonic during run
assert property ( active && $past(active) |-> cycle == $past(cycle)-5'd1 )
  else $error("DIV: Bad cycle decrement");

// Denominator and flags stable during run
assert property ( active && $past(active) |-> $stable(denominator) && $stable(neg_result) && $stable(neg_remainder) )
  else $error("DIV: Denominator/flags changed while active");

// Iteration update semantics
assert property ( ($past(active) && !$past(op_divs) && !$past(op_divu) && $past(partial_sub[32])==1'b0)
                  |-> (residual==$past(partial_sub[31:0]) &&
                       result=={ $past(result[30:0]), 1'b1 }) )
  else $error("DIV: Update mismatch (sub >= 0)");

assert property ( ($past(active) && !$past(op_divs) && !$past(op_divu) && $past(partial_sub[32])==1'b1)
                  |-> (residual=={ $past(residual[30:0]), $past(result[31]) } &&
                       result=={ $past(result[30:0]), 1'b0 }) )
  else $error("DIV: Update mismatch (sub < 0)");

// Output sign-correction mapping (combinational)
assert property ( quotient  == (neg_result    ? -result   : result) )
  else $error("DIV: Quotient sign-correction mismatch");
assert property ( remainder == (neg_remainder ? -residual : residual) )
  else $error("DIV: Remainder sign-correction mismatch");

// Final arithmetic correctness at completion (unsigned)
property p_divu_correct;
  logic [31:0] dvnd, dvsr;
  (op_divu && !active, dvnd=dividend, dvsr=divisor)
  |-> ##1 active[*32] ##1 (!active && $past(active))
      ##0 ( (dvsr!=0) -> (quotient == (dvnd / dvsr) &&
                          remainder == (dvnd % dvsr) &&
                          remainder < dvsr) );
endproperty
assert property (p_divu_correct)
  else $error("DIVU: Incorrect quotient/remainder");

// Final arithmetic correctness at completion (signed)
property p_divs_correct;
  logic [31:0] dvnd, dvsr;
  (op_divs && !active, dvnd=dividend, dvsr=divisor)
  |-> ##1 active[*32] ##1 (!active && $past(active))
      ##0 ( (dvsr!=0) -> ( $signed(quotient)  == ($signed(dvnd) / $signed(dvsr)) &&
                           $signed(remainder) == ($signed(dvnd) % $signed(dvsr)) &&
                           ( ($signed(remainder)==0) ||
                             (remainder[31] == dvnd[31]) ) &&
                           (abs32(remainder) < abs32(dvsr)) ) );
endproperty
assert property (p_divs_correct)
  else $error("DIVS: Incorrect quotient/remainder");

// Coverage
cover property (op_divu && !active);
cover property (op_divs && !active);
cover property (op_divs && !active &&  dividend[31] && !divisor[31]); // neg/pos
cover property (op_divs && !active && !dividend[31] &&  divisor[31]); // pos/neg
cover property (start_div ##1 active[*32] ##1 !active);                // 32-cycle run
// Remainder zero cases
property c_rem0_u;
  logic [31:0] dvnd, dvsr;
  (op_divu && !active, dvnd=dividend, dvsr=divisor)
  |-> ##1 active[*32] ##1 (!active && $past(active)) ##0 (dvsr!=0 && remainder==32'h0);
endproperty
cover property (c_rem0_u);
property c_rem0_s;
  logic [31:0] dvnd, dvsr;
  (op_divs && !active, dvnd=dividend, dvsr=divisor)
  |-> ##1 active[*32] ##1 (!active && $past(active)) ##0 (dvsr!=0 && remainder==32'h0);
endproperty
cover property (c_rem0_s);
// Edge case: MIN_INT / -1 (wrap behavior)
cover property (op_divs && !active && dividend==32'h8000_0000 && divisor==32'hFFFF_FFFF);

`endif