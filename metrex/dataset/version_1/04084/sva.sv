// SVA for full_adder and four_bit_adder (bind-ready)

module full_adder_sva(input logic a, b, carry_in, sum, carry_out);
  always_comb begin
    if (!$isunknown({a,b,carry_in,sum,carry_out})) begin
      logic [1:0] exp; exp = a + b + carry_in;
      assert (sum == (a ^ b ^ carry_in)) else $error("full_adder: sum mismatch");
      assert (carry_out == ((a & b) | (a & carry_in) | (b & carry_in))) else $error("full_adder: carry mismatch");
      assert ({carry_out, sum} == exp) else $error("full_adder: 2-bit add mismatch");
      assert ((a & b) -> carry_out) else $error("full_adder: generate must set carry");
      assert ((~a & ~b) -> !carry_out) else $error("full_adder: kill must clear carry");
      assert ((a ^ b) -> (carry_out == carry_in && sum == ~carry_in)) else $error("full_adder: propagate behavior wrong");
    end
    // basic coverage
    cover (a & b);
    cover (~a & ~b);
    cover (a ^ b);
    cover ({a,b,carry_in} == 3'b000);
    cover ({a,b,carry_in} == 3'b111);
  end
endmodule

module four_bit_adder_sva(
  input logic [3:0] a, b,
  input logic [3:0] sum,
  input logic       carry_out,
  input logic [3:0] fa_sum,
  input logic [3:0] fa_carry_out
);
  always_comb begin
    if (!$isunknown({a,b,sum,carry_out,fa_sum,fa_carry_out})) begin
      logic [4:0] exp; exp = a + b;
      assert ({carry_out, sum} == exp) else $error("four_bit_adder: result != a+b");
      assert (sum == fa_sum) else $error("four_bit_adder: sum != fa_sum bus");
      // LSB
      assert (fa_sum[0] == (a[0] ^ b[0])) else $error("bit0 sum wrong");
      assert (fa_carry_out[0] == (a[0] & b[0])) else $error("bit0 carry wrong");
      // ripple stages
      assert (fa_sum[1] == (a[1] ^ b[1] ^ fa_carry_out[0])) else $error("bit1 sum wrong");
      assert (fa_carry_out[1] == ((a[1] & b[1]) | ((a[1]^b[1]) & fa_carry_out[0]))) else $error("bit1 carry wrong");
      assert (fa_sum[2] == (a[2] ^ b[2] ^ fa_carry_out[1])) else $error("bit2 sum wrong");
      assert (fa_carry_out[2] == ((a[2] & b[2]) | ((a[2]^b[2]) & fa_carry_out[1]))) else $error("bit2 carry wrong");
      assert (fa_sum[3] == (a[3] ^ b[3] ^ fa_carry_out[2])) else $error("bit3 sum wrong");
      assert (carry_out == ((a[3] & b[3]) | ((a[3]^b[3]) & fa_carry_out[2]))) else $error("MSB carry wrong");
    end
    // key coverage
    cover (carry_out);
    cover (a==4'h0 && b==4'h0 && sum==4'h0 && !carry_out);
    cover (a==4'hF && b==4'hF && carry_out && sum==4'hE);
    // full ripple from bit0 through bit3 (generate at bit0, propagate 1..3)
    cover ( (a[0]&b[0]) &&
            (a[1]^b[1]) && !(a[1]&b[1]) &&
            (a[2]^b[2]) && !(a[2]&b[2]) &&
            (a[3]^b[3]) && !(a[3]&b[3]) );
  end
endmodule

bind full_adder     full_adder_sva(.a(a), .b(b), .carry_in(carry_in), .sum(sum), .carry_out(carry_out));
bind four_bit_adder four_bit_adder_sva(.a(a), .b(b), .sum(sum), .carry_out(carry_out), .fa_sum(fa_sum), .fa_carry_out(fa_carry_out));