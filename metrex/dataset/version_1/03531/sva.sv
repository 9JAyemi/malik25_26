// SVA for adder_16bit_signed_unsigned
module adder_16bit_signed_unsigned_sva (
  input  signed [15:0] a,
  input  signed [15:0] b,
  input                cin,
  input  signed [15:0] sum,
  input                cout
);
  logic [16:0] ufull;          // unsigned-extended full sum
  logic signed [16:0] sfull;   // signed-extended full sum

  assign ufull = {1'b0, a} + {1'b0, b} + cin;
  assign sfull = $signed({a[15],a}) + $signed({b[15],b}) + $signed({16'd0,cin});

  // Core correctness checks
  always_comb begin
    assert #0 (sum === ufull[15:0]) else
      $error("sum mismatch: got %0d exp %0d (a=%0d b=%0d cin=%0b)", sum, ufull[15:0], a, b, cin);

    assert #0 (cout === ufull[16]) else
      $error("cout mismatch: got %0b exp %0b (a=%0d b=%0d cin=%0b)", cout, ufull[16], a, b, cin);

    if (!$isunknown({a,b,cin})) begin
      assert #0 (!$isunknown({sum,cout})) else
        $error("X/Z on outputs with known inputs (a=%h b=%h cin=%b)", a, b, cin);
    end
  end

  // Functional coverage (procedural cover)
  always_comb begin
    // cin polarity and carry-out
    cover (cin == 0);
    cover (cin == 1);
    cover (cout == 1);

    // Signed overflow cases (pos+pos->neg, neg+neg->pos)
    cover ((a[15]==0) && (b[15]==0) && (sum[15]==1));
    cover ((a[15]==1) && (b[15]==1) && (sum[15]==0));

    // Mixed-sign, both orders, and with cin asserted
    cover ((a[15]^b[15]) && (cin==0));
    cover ((a[15]^b[15]) && (cin==1));

    // Boundary/regression points
    cover ((a==16'sh7FFF) && (b==16'sh0001) && (cin==0));
    cover ((a==16'sh8000) && (b==16'sh8000) && (cin==0));
    cover ((a==16'shFFFF) && (b==16'sh0001) && (cin==1));
  end
endmodule

// Bind into the DUT
bind adder_16bit_signed_unsigned adder_16bit_signed_unsigned_sva (.*);