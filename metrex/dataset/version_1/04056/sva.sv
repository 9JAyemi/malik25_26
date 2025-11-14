// SVA checker for adder_4bit
module adder_4bit_sva(input [3:0] a, b, input cin, input [3:0] sum, input cout);
  logic c1, c2, c3;
  logic [4:0] exp5;
  always_comb begin
    // expected ripple-carry chain
    c1   = (a[0] & b[0]) | (a[0] & cin) | (b[0] & cin);
    c2   = (a[1] & b[1]) | (a[1] & c1 ) | (b[1] & c1 );
    c3   = (a[2] & b[2]) | (a[2] & c2 ) | (b[2] & c2 );
    exp5 = a + b + cin;

    if (!$isunknown({a,b,cin})) begin
      // Golden 5-bit equivalence (flags the DUT bug if present)
      assert ({cout, sum} == exp5)
        else $error("Adder mismatch: a=%0h b=%0h cin=%0b exp={C,S}=%0h got C=%0b S=%0h",
                    a,b,cin,exp5,cout,sum);

      // Bit-accurate checks derived from inputs
      assert (sum[0] == (a[0] ^ b[0] ^ cin));
      assert (sum[1] == (a[1] ^ b[1] ^ c1));
      assert (sum[2] == (a[2] ^ b[2] ^ c2));
      assert (sum[3] == (a[3] ^ b[3] ^ c3));
      assert (cout    == c3);

      // No X/Z on outputs when inputs are known
      assert (!$isunknown({sum,cout}))
        else $error("Unknown on outputs with known inputs: a=%0h b=%0h cin=%0b S=%0h C=%0b",
                    a,b,cin,sum,cout);
    end

    // Minimal functional coverage
    cover ({a,b,cin} == 9'b0);                     // all zeros
    cover (a==4'hF && b==4'h0 && cin==0);          // max + zero
    cover (a==4'h0 && b==4'hF && cin==0);          // zero + max
    cover (a==4'hF && b==4'hF && cin==1);          // worst-case overflow

    // Carry behavior coverage
    cover (c1 && !c2);     // carry generated at bit0 only
    cover (c2 && !c3);     // carry generated at bit1 only
    cover (c3);            // carry into MSB
    cover ((a[3] & b[3]) | (a[3] & c3) | (b[3] & c3)); // final overflow expected
  end
endmodule

// Bind the checker to the DUT
bind adder_4bit adder_4bit_sva sva_i(.*);