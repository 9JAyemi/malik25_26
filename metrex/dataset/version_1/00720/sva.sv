// SVA checker for addition_4bit
module addition_4bit_sva (
  input  logic [3:0] a,
  input  logic [3:0] b,
  input  logic [3:0] sum
);
  logic [4:0] full_sum = {1'b0,a} + {1'b0,b};

  // Interface sanity and functional correctness (mod-16)
  always_comb begin
    assert (!$isunknown({a,b,sum})) else
      $error("addition_4bit: X/Z on ports a=%b b=%b sum=%b", a,b,sum);

    if (!$isunknown({a,b}))
      assert (sum == full_sum[3:0]) else
        $error("addition_4bit: sum=%0d expected=%0d (a=%0d b=%0d)", sum, full_sum[3:0], a, b);
  end

  // Key scenario coverage: carry/no-carry
  always_comb begin
    cover (full_sum[4] == 0);
    cover (full_sum[4] == 1);
  end

  // Full input-space coverage (all 256 a,b pairs)
  genvar i,j;
  generate
    for (i=0; i<16; i++) begin : COV_AB_I
      for (j=0; j<16; j++) begin : COV_AB_J
        always_comb cover ((a == i[3:0]) && (b == j[3:0]));
      end
    end
  endgenerate

  // All sum values observed
  genvar s;
  generate
    for (s=0; s<16; s++) begin : COV_SUM_S
      always_comb cover (sum == s[3:0]);
    end
  endgenerate
endmodule

// Bind the checker to the DUT
bind addition_4bit addition_4bit_sva u_addition_4bit_sva (.a(a), .b(b), .sum(sum));