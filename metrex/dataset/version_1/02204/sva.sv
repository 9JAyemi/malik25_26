// SVA for four_bit_adder
// Bind-in assertions; no DUT changes required.

module four_bit_adder_sva (
  input  logic [3:0] a,
  input  logic [3:0] b,
  input  logic       cin,
  input  logic [3:0] sum,
  input  logic       cout,
  input  logic [3:0] c // internal carry vector from DUT
);

  // Sample on any input change
  event samp;
  always @(a or b or cin) -> samp;

  // Golden ripple-carry model
  logic       carry0, carry1, carry2, carry3, cout_exp;
  logic [3:0] sum_exp;

  assign carry0  = cin;
  assign sum_exp[0] = a[0] ^ b[0] ^ carry0;
  assign carry1  = (a[0] & b[0]) | ((a[0] ^ b[0]) & carry0);

  assign sum_exp[1] = a[1] ^ b[1] ^ carry1;
  assign carry2  = (a[1] & b[1]) | ((a[1] ^ b[1]) & carry1);

  assign sum_exp[2] = a[2] ^ b[2] ^ carry2;
  assign carry3  = (a[2] & b[2]) | ((a[2] ^ b[2]) & carry2);

  assign sum_exp[3] = a[3] ^ b[3] ^ carry3;
  assign cout_exp = (a[3] & b[3]) | ((a[3] ^ b[3]) & carry3);

  // Functional correctness (5-bit result)
  property p_total;
    @(samp) (!$isunknown({a,b,cin})) |-> ({cout,sum} == a + b + cin);
  endproperty
  assert property (p_total)
    else $error("Adder mismatch: a=%0h b=%0h cin=%0b got {cout,sum}=%0h exp=%0h",
                a,b,cin,{cout,sum}, (a+b+cin));

  // No X/Z on outputs (and internals) when inputs are known
  property p_no_x;
    @(samp) (!$isunknown({a,b,cin})) |-> (!$isunknown({sum,cout,c}));
  endproperty
  assert property (p_no_x)
    else $error("X/Z detected on outputs/internal c with known inputs: a=%0h b=%0h cin=%0b sum=%0h cout=%0b c=%0h",
                a,b,cin,sum,cout,c);

  // Internal carry chain must be correct
  property p_c0;  @(samp) (!$isunknown({a,b,cin})) |-> (c[0] == carry0); endproperty
  property p_c1;  @(samp) (!$isunknown({a,b,cin})) |-> (c[1] == carry1); endproperty
  property p_c2;  @(samp) (!$isunknown({a,b,cin})) |-> (c[2] == carry2); endproperty
  property p_c3;  @(samp) (!$isunknown({a,b,cin})) |-> (c[3] == carry3); endproperty
  property p_cout;@(samp) (!$isunknown({a,b,cin})) |-> (cout == cout_exp); endproperty

  assert property (p_c0) else $error("c[0] mismatch: exp=%0b got=%0b", carry0, c[0]);
  assert property (p_c1) else $error("c[1] mismatch: exp=%0b got=%0b", carry1, c[1]);
  assert property (p_c2) else $error("c[2] mismatch: exp=%0b got=%0b", carry2, c[2]);
  assert property (p_c3) else $error("c[3] mismatch: exp=%0b got=%0b", carry3, c[3]);
  assert property (p_cout) else $error("cout mismatch: exp=%0b got=%0b", cout_exp, cout);

  // Concise functional coverage
  cover property (@(samp) (!$isunknown({a,b,cin})) && (cin == 1'b0));
  cover property (@(samp) (!$isunknown({a,b,cin})) && (cin == 1'b1));
  cover property (@(samp) (!$isunknown({a,b,cin})) && (cout == 1'b0));
  cover property (@(samp) (!$isunknown({a,b,cin})) && (cout == 1'b1));

  // Corner scenarios
  cover property (@(samp) (!$isunknown({a,b,cin})) && (a==4'h0) && (b==4'h0) && (cin==1'b0) && ({cout,sum}==5'd0));
  cover property (@(samp) (!$isunknown({a,b,cin})) && ({cout,sum}==5'd31)); // max result
  // Full propagate chain causing ripple to MSB
  cover property (@(samp) (!$isunknown({a,b,cin})) && ((a^b)==4'hF) && (cin==1'b1) && (cout==1'b1));
  // Direct MSB generate
  cover property (@(samp) (!$isunknown({a,b,cin})) && (a[3]&b[3]) && (cout==1'b1));

endmodule

// Bind into the DUT
bind four_bit_adder four_bit_adder_sva sva (
  .a(a), .b(b), .cin(cin), .sum(sum), .cout(cout), .c(c)
);