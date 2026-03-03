// SVA bind module for full_adder
module full_adder_sva (
  input logic a, b, cin,
  input logic s, cout,
  input logic c1, c2
);

  // Combinational, 4-state safe checks
  always_comb begin
    // No X/Z on IOs
    assert (!$isunknown({a,b,cin,s,cout}))
      else $error("full_adder: X/Z detected on IOs a=%b b=%b cin=%b s=%b cout=%b", a,b,cin,s,cout);

    // Internal terms
    assert (c1 === (a & b))
      else $error("full_adder: c1 mismatch: c1=%b a&b=%b", c1, (a&b));
    assert (c2 === (cin & (a ^ b)))
      else $error("full_adder: c2 mismatch: c2=%b cin&(a^b)=%b", c2, (cin & (a^b)));

    // Output composition
    assert (cout === (c1 | c2))
      else $error("full_adder: cout != c1|c2: cout=%b c1=%b c2=%b", cout,c1,c2);

    // Functional equivalence (redundant forms)
    assert (s === (a ^ b ^ cin))
      else $error("full_adder: s != a^b^cin");
    assert (cout === ((a & b) | (a & cin) | (b & cin)))
      else $error("full_adder: cout != majority(a,b,cin)");
    assert ({cout,s} === (a + b + cin))
      else $error("full_adder: {cout,s} != a+b+cin");
  end

  // Compact functional coverage (all input tuples, all output tuples, internal term activity)
  always_comb begin
    cover ({a,b,cin} == 3'b000);
    cover ({a,b,cin} == 3'b001);
    cover ({a,b,cin} == 3'b010);
    cover ({a,b,cin} == 3'b011);
    cover ({a,b,cin} == 3'b100);
    cover ({a,b,cin} == 3'b101);
    cover ({a,b,cin} == 3'b110);
    cover ({a,b,cin} == 3'b111);

    cover ({cout,s} == 2'b00);
    cover ({cout,s} == 2'b01);
    cover ({cout,s} == 2'b10);
    cover ({cout,s} == 2'b11);

    cover (c1); // generate observed
    cover (c2); // propagate-with-cin observed
  end

endmodule

// Bind into the DUT (captures internal c1/c2 as well)
bind full_adder full_adder_sva sva (.*);