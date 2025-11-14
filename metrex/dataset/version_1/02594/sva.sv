// SVA checkers and binds for the given design.
// Purely combinational: use immediate assertions/covers in always_comb.

package top_sva_pkg;
  function automatic signed [3:0] add4(input signed [3:0] a, b);
    add4 = $signed(a) + $signed(b);
  endfunction
  function automatic bit ovf4(input signed [3:0] a, b);
    ovf4 = (a[3] == b[3]) && (add4(a,b)[3] != a[3]);
  endfunction
endpackage

import top_sva_pkg::*;

// Comparator checker
module sva_signed_comparator(
  input signed [3:0] A, B,
  input eq, gt, lt
);
  always_comb begin
    assert (!$isunknown({A,B,eq,gt,lt})) else $error("X/Z detected in comparator IO");
    assert (eq == ($signed(A) == $signed(B))) else $error("eq mismatch");
    assert (gt == ($signed(A) >  $signed(B))) else $error("gt mismatch");
    assert (lt == ($signed(A) <  $signed(B))) else $error("lt mismatch");
    assert ({eq,gt,lt} inside {3'b100,3'b010,3'b001}) else $error("eq/gt/lt not one-hot");
    cover (eq);
    cover (gt);
    cover (lt);
  end
endmodule

// Adder checker
module sva_signed_adder(
  input signed [3:0] A, B,
  input signed [3:0] out,
  input overflow
);
  always_comb begin
    assert (!$isunknown({A,B,out,overflow})) else $error("X/Z detected in adder IO");
    assert ($signed(out) == add4(A,B)) else $error("adder out != A+B (truncated 4b signed)");
    assert (overflow == ovf4(A,B)) else $error("signed overflow flag incorrect");
    cover (overflow);
    cover (!overflow);
  end
endmodule

// Top-level checker (re-asserts key leaf behavior and mux/select logic)
module sva_top_module(
  input signed [3:0] A, B,
  input signed [3:0] sum,   // internal top wire from adder
  input signed [3:0] out,
  input eq, gt, lt,
  input overflow
);
  always_comb begin
    assert (!$isunknown({A,B,sum,out,eq,gt,lt,overflow})) else $error("X/Z detected in top signals");
    // Comparator consistency
    assert (eq == ($signed(A) == $signed(B))) else $error("top eq mismatch");
    assert (gt == ($signed(A) >  $signed(B))) else $error("top gt mismatch");
    assert (lt == ($signed(A) <  $signed(B))) else $error("top lt mismatch");
    assert ({eq,gt,lt} inside {3'b100,3'b010,3'b001}) else $error("top eq/gt/lt not one-hot");
    // Adder consistency as observed at top
    assert ($signed(sum) == add4(A,B)) else $error("top sum != A+B");
    assert (overflow == ovf4(A,B)) else $error("top overflow incorrect");
    // Mux behavior
    assert ($signed(out) == (eq ? $signed(sum) : (gt ? $signed(A) : $signed(B))))
      else $error("top mux out mismatch");

    // Coverage: select paths and overflow corner cases
    cover (eq && (out == sum));
    cover (gt && (out == A));
    cover (lt && (out == B));
    cover (($signed(A) > 0) && ($signed(B) > 0) && overflow);  // positive overflow
    cover (($signed(A) < 0) && ($signed(B) < 0) && overflow);  // negative overflow
    cover ($signed(A) == 4'sd7 && $signed(B) == 4'sd1);        // +7 +1
    cover ($signed(A) == -4'sd8 && $signed(B) == -4'sd1);      // -8 -1
    cover ($signed(A) == 0 && $signed(B) == 0);                // zero case
  end
endmodule

// Bind checkers
bind signed_comparator sva_signed_comparator u_sva_signed_comparator(
  .A(A), .B(B), .eq(eq), .gt(gt), .lt(lt)
);

bind signed_adder sva_signed_adder u_sva_signed_adder(
  .A(A), .B(B), .out(out), .overflow(overflow)
);

bind top_module sva_top_module u_sva_top_module(
  .A(A), .B(B), .sum(sum), .out(out), .eq(eq), .gt(gt), .lt(lt), .overflow(overflow)
);