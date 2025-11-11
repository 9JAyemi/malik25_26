// SVA for adder
checker adder_sva (
  input logic [7:0]  a,
  input logic [7:0]  b,
  input logic [15:0] sum_in,
  input logic [7:0]  sum,
  input logic        carry
);
  always_comb begin
    let trunc_sum16 = sum_in + {a,b};                 // 16-bit add per RTL
    let full_sum17  = {1'b0,sum_in} + {1'b0,a,b};     // 17-bit mathematically correct sum

    // Functional check of implemented behavior (including width truncation)
    assert #0 ({carry, sum} == trunc_sum16[8:0])
      else $error("adder SVA: {carry,sum} != (sum_in + {a,b})[8:0]");

    // Sanity: no X/Z on any ports
    assert #0 (!$isunknown({a,b,sum_in,sum,carry}))
      else $error("adder SVA: X/Z detected on ports");

    // Coverage: exercise key scenarios and highlight potential intent mismatch
    cover (carry);
    cover (!carry);
    cover (|trunc_sum16[15:9]);              // upper bits of 16-bit result are non-zero (information truncated by RTL)
    cover (full_sum17[16]);                  // true 17-bit carry-out exists
    cover (full_sum17[16] != carry);         // implemented carry differs from true 17-bit carry-out
    cover (sum == 8'h00);
    cover (sum == 8'hFF);
  end
endchecker

bind adder adder_sva adder_sva_i (.*);