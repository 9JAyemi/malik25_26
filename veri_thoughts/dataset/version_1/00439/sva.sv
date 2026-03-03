// SVA checkers and binds for adder_mux design
// Focused, concise, and with key functional coverage

// Checker for top-level adder_mux (checks muxing and end-to-end sum)
module adder_mux_sva (
  input  logic [3:0] a,
  input  logic [3:0] b,
  input  logic       control,
  input  logic [3:0] sum,
  input  logic [3:0] sum1,
  input  logic [3:0] sum2
);
  logic [4:0] exp;
  always_comb begin
    exp = a + b;

    // Functional correctness
    assert (#0 (sum1 === exp[3:0])) else $error("adder_mux: sum1 != a+b");
    assert (#0 (sum2 === exp[3:0])) else $error("adder_mux: sum2 != a+b");
    assert (#0 (sum1 === sum2))     else $error("adder_mux: sum1 != sum2");
    assert (#0 (sum  === (control ? sum2 : sum1))) else $error("adder_mux: mux select mismatch");
    assert (#0 (sum  === exp[3:0])) else $error("adder_mux: sum != a+b");

    // X-propagation sanity
    if (!$isunknown({a,b,control})) assert (#0 !$isunknown(sum)) else $error("adder_mux: known inputs -> X/Z sum");

    // Coverage
    cover (control == 0);
    cover (control == 1);
    cover (exp[4] == 1'b1);       // overflow occurred
    cover (exp[3:0] == 4'h0);     // zero result
    cover (exp[3:0] == 4'hF);     // max result
  end
endmodule

// Checker for four_bit_adder (end-to-end and ripple-carry bit relations)
module four_bit_adder_sva (
  input  logic [3:0] a,
  input  logic [3:0] b,
  input  logic [3:0] sum,
  input  logic       c1,
  input  logic       c2,
  input  logic       c3
);
  logic [4:0] exp;
  logic       c1_exp, c2_exp, c3_exp;
  always_comb begin
    exp    = a + b;
    c1_exp = a[0] & b[0];
    c2_exp = (a[1] & b[1]) | (a[1] & c1_exp) | (b[1] & c1_exp);
    c3_exp = (a[2] & b[2]) | (a[2] & c2_exp) | (b[2] & c2_exp);

    // End-to-end
    assert (#0 (sum === exp[3:0])) else $error("four_bit_adder: sum != a+b");

    // Ripple-carry structure
    assert (#0 (sum[0] === (a[0] ^ b[0]))) else $error("four_bit_adder: sum[0] mismatch");
    assert (#0 (c1     === c1_exp))        else $error("four_bit_adder: c1 mismatch");
    assert (#0 (sum[1] === (a[1] ^ b[1] ^ c1))) else $error("four_bit_adder: sum[1] mismatch");
    assert (#0 (c2     === c2_exp))        else $error("four_bit_adder: c2 mismatch");
    assert (#0 (sum[2] === (a[2] ^ b[2] ^ c2))) else $error("four_bit_adder: sum[2] mismatch");
    assert (#0 (c3     === c3_exp))        else $error("four_bit_adder: c3 mismatch");
    assert (#0 (sum[3] === (a[3] ^ b[3] ^ c3))) else $error("four_bit_adder: sum[3] mismatch");

    // X-propagation sanity
    if (!$isunknown({a,b})) assert (#0 !$isunknown(sum)) else $error("four_bit_adder: known inputs -> X/Z sum");

    // Coverage
    cover (exp[4] == 1'b1);       // overflow out of MSB
    cover (exp[3:0] == 4'h0);
    cover (exp[3:0] == 4'hF);
  end
endmodule

// Checker for full_adder (truth table and X checks)
module full_adder_sva (
  input  logic a,
  input  logic b,
  input  logic cin,
  input  logic sum,
  input  logic cout
);
  always_comb begin
    // Functional truth
    assert (#0 (sum  === (a ^ b ^ cin)))                       else $error("full_adder: sum mismatch");
    assert (#0 (cout === ((a & b) | (a & cin) | (b & cin))))   else $error("full_adder: cout mismatch");

    // X-propagation sanity
    if (!$isunknown({a,b,cin})) assert (#0 !$isunknown({sum,cout})) else $error("full_adder: known inputs -> X/Z outputs");

    // Coverage: all 8 input combinations
    cover ({a,b,cin} == 3'b000);
    cover ({a,b,cin} == 3'b001);
    cover ({a,b,cin} == 3'b010);
    cover ({a,b,cin} == 3'b011);
    cover ({a,b,cin} == 3'b100);
    cover ({a,b,cin} == 3'b101);
    cover ({a,b,cin} == 3'b110);
    cover ({a,b,cin} == 3'b111);
  end
endmodule

// Bind the checkers into the DUT hierarchy
bind adder_mux     adder_mux_sva      u_adder_mux_sva      (.a(a), .b(b), .control(control), .sum(sum), .sum1(sum1), .sum2(sum2));
bind four_bit_adder four_bit_adder_sva u_four_bit_adder_sva (.a(a), .b(b), .sum(sum), .c1(c1), .c2(c2), .c3(c3));
bind full_adder    full_adder_sva     u_full_adder_sva     (.a(a), .b(b), .cin(cin), .sum(sum), .cout(cout));