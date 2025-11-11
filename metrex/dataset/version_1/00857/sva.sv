// SVA checkers and binds for adder_4bit_carry and full_adder

module full_adder_sva;
  // Bound into full_adder scope: a,b,cin,sum,cout visible
  always_comb begin
    if (!$isunknown({a,b,cin})) begin
      assert (sum  === (a ^ b ^ cin))
        else $error("full_adder sum mismatch a=%0b b=%0b cin=%0b sum=%0b", a,b,cin,sum);
      assert (cout === ((a & b) | (cin & (a ^ b))))
        else $error("full_adder cout mismatch a=%0b b=%0b cin=%0b cout=%0b", a,b,cin,cout);
    end
    if (!$isunknown({a,b,cin})) assert (!$isunknown({sum,cout}))
      else $error("full_adder X/Z outputs with known inputs a=%0b b=%0b cin=%0b", a,b,cin);

    // Minimal coverage on FA behavior
    cover (a & b);                 // generate
    cover ((a ^ b) & cin);         // propagate
    cover (!a & !b & !cin);        // kill
  end
endmodule

module adder_4bit_carry_sva;
  // Bound into adder_4bit_carry scope: a,b,cin,sum,cout,temp_sum,c1,c2,c3 visible
  logic [4:0] gold;
  always_comb begin
    gold = a + b + cin;

    if (!$isunknown({a,b,cin})) begin
      assert ({cout,sum} == gold)
        else $error("adder_4bit_carry mismatch a=%0h b=%0h cin=%0b got {cout,sum}=%0h exp=%0h",
                    a,b,cin,{cout,sum},gold);

      // Bitwise sums and ripple carries
      assert (temp_sum[0] === (a[0]^b[0]^cin));
      assert (temp_sum[1] === (a[1]^b[1]^c1));
      assert (temp_sum[2] === (a[2]^b[2]^c2));
      assert (temp_sum[3] === (a[3]^b[3]^c3));

      assert (c1  === ((a[0]&b[0]) | (cin & (a[0]^b[0]))));
      assert (c2  === ((a[1]&b[1]) | (c1  & (a[1]^b[1]))));
      assert (c3  === ((a[2]&b[2]) | (c2  & (a[2]^b[2]))));
      assert (cout=== ((a[3]&b[3]) | (c3  & (a[3]^b[3]))));
    end

    assert (sum === temp_sum) else $error("sum != temp_sum");
    if (!$isunknown({a,b,cin})) assert (!$isunknown({sum,cout,temp_sum,c1,c2,c3}))
      else $error("adder_4bit_carry X/Z outputs with known inputs");

    // Focused coverage
    cover (gold == 5'h00);                  // 0+0+0
    cover (gold == 5'h1F);                  // 15+15+1 (overflow)
    cover (cout && (sum == 4'h0));          // wrap-around
    cover ((cin==1'b1) && ((a^b)==4'hF));   // full propagate chain
    cover (|(a & b));                       // any generate
  end
endmodule

bind full_adder       full_adder_sva       fa_sva();
bind adder_4bit_carry adder_4bit_carry_sva add4_sva();