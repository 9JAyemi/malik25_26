// SVA for add_subtract: concise, high-quality checks and coverage
module add_subtract_sva (
  input logic [7:0] a,
  input logic [7:0] b,
  input logic       sel,
  input logic [7:0] out
);

  // Functional correctness on any input change (allow 0-delay settle)
  property p_add;
    @(a or b or sel)
      (!$isunknown({a,b,sel}) && sel) |-> ##0 (out == ((a + b) & 8'hFF));
  endproperty
  assert property (p_add);

  property p_sub;
    @(a or b or sel)
      (!$isunknown({a,b,sel}) && !sel) |-> ##0 (out == ((a - b) & 8'hFF));
  endproperty
  assert property (p_sub);

  // Output must not be X/Z when inputs are known
  property p_no_x;
    @(a or b or sel)
      (!$isunknown({a,b,sel})) |-> ##0 (!$isunknown(out));
  endproperty
  assert property (p_no_x);

  // Output stable if inputs are stable (sampled on global clock)
  assert property (@(posedge $global_clock) $stable({a,b,sel}) |-> $stable(out));

  // Coverage: exercise add/sub, with/without carry/borrow, and key edge cases
  cover property (@(a or b or sel) (!$isunknown({a,b,sel}) && sel && !({1'b0,a}+{1'b0,b})[8]) ##0 (out == ((a + b) & 8'hFF))); // add no-carry
  cover property (@(a or b or sel) (!$isunknown({a,b,sel}) && sel &&  ({1'b0,a}+{1'b0,b})[8]) ##0 (out == ((a + b) & 8'hFF))); // add carry
  cover property (@(a or b or sel) (!$isunknown({a,b,sel}) && !sel && (a >= b)) ##0 (out == ((a - b) & 8'hFF)));            // sub no-borrow
  cover property (@(a or b or sel) (!$isunknown({a,b,sel}) && !sel && (a <  b)) ##0 (out == ((a - b) & 8'hFF)));            // sub borrow
  cover property (@(a or b or sel) (!$isunknown({a,b,sel}) && !sel && (a == b)) ##0 (out == 8'h00));                        // subtract to zero
  cover property (@(a or b or sel) (!$isunknown({a,b,sel}) && sel && ((a==8'h00)||(b==8'h00))) ##0 (out == ((a + b) & 8'hFF))); // add with zero
endmodule

bind add_subtract add_subtract_sva sva_inst (.a(a), .b(b), .sel(sel), .out(out));