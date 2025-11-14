// SVA checker for top_module
module top_module_sva (
  input  logic [7:0]  a, b, c, d,
  input  logic [7:0]  min1, min2, min3, min4, min12, min34, min1234,
  input  logic [31:0] num1, num2, sum, diff, result,
  input  logic        sub
);

  function automatic logic [7:0] umin2 (input logic [7:0] x, y);
    return (x < y) ? x : y;
  endfunction

  function automatic logic [7:0] umin4 (input logic [7:0] w, x, y, z);
    logic [7:0] m1, m2;
    m1 = umin2(w, x);
    m2 = umin2(y, z);
    return umin2(m1, m2);
  endfunction

  function automatic logic [31:0] zext8 (input logic [7:0] v);
    return {24'b0, v};
  endfunction

  // Combinational assertions
  always_comb begin
    // Pairwise mins/maxs
    assert (min1 == umin2(a, b)) else $error("min1 != min(a,b)");
    assert (min2 == ((a < b) ? b : a)) else $error("min2 != max(a,b)");
    assert (min3 == umin2(c, d)) else $error("min3 != min(c,d)");
    assert (min4 == ((c < d) ? d : c)) else $error("min4 != max(c,d)");

    // Tree structure
    assert (min12 == umin2(min1, min3)) else $error("min12 wrong");
    assert (min34 == umin2(min2, min4)) else $error("min34 wrong");
    assert (min1234 == umin2(min12, min34)) else $error("min1234 wrong");

    // Global min correctness
    assert (min1234 == umin4(a, b, c, d)) else $error("min1234 != min(a,b,c,d)");
    assert (min1 <= min2) else $error("min1 > min2");
    assert (min3 <= min4) else $error("min3 > min4");
    assert (min12 <= min34) else $error("min12 > min34");
    assert ((min1234==a)||(min1234==b)||(min1234==c)||(min1234==d))
      else $error("min1234 not one of inputs");

    // Arithmetic blocks
    assert (sum  == (num1 + num2)) else $error("sum wrong");
    assert (diff == (num1 - num2)) else $error("diff wrong");

    // Final result checks (independent and via internal sum/diff)
    assert (result == (sub ? (zext8(min1234) - diff)
                           : (zext8(min1234) + sum)))
      else $error("result path wrong (using sum/diff)");

    assert (result == (sub ? (zext8(min1234) - (num1 - num2))
                           : (zext8(min1234) + (num1 + num2))))
      else $error("result wrong vs direct computation");
  end

  // Simple coverage
  always_comb begin
    cover (a < b);
    cover (a == b);
    cover (c < d);
    cover (c == d);
    cover (min1234 == a);
    cover (min1234 == b);
    cover (min1234 == c);
    cover (min1234 == d);
    cover (sub == 1'b0);
    cover (sub == 1'b1);
    cover ((num1 + num2) < num1); // add overflow
    cover (num1 < num2);          // sub underflow
  end

endmodule

// Bind into DUT to observe internal nets
bind top_module top_module_sva sva_i (
  .a(a), .b(b), .c(c), .d(d),
  .min1(min1), .min2(min2), .min3(min3), .min4(min4),
  .min12(min12), .min34(min34), .min1234(min1234),
  .num1(num1), .num2(num2), .sum(sum), .diff(diff), .result(result),
  .sub(sub)
);