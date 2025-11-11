// SVA for ripple_adder: concise, high-quality functional checks + basic coverage

module ripple_adder_sva (
  input  logic [3:0] a,
  input  logic [3:0] b,
  input  logic       cin,
  input  logic [3:0] sum,
  input  logic       cout
);
  logic [4:0] expected; // 5-bit golden sum (includes carry)

  always_comb begin
    expected = {1'b0, a} + {1'b0, b} + cin;

    // Functional correctness (only check when inputs are known)
    if (!$isunknown({a,b,cin})) begin
      assert ({cout, sum} === expected)
        else $error("ripple_adder mismatch: a=%0h b=%0h cin=%0b exp={cout,sum}=%0h got=%0h",
                    a, b, cin, expected, {cout, sum});
      assert (!$isunknown({sum,cout}))
        else $error("ripple_adder produced X/Z on outputs with known inputs");
    end

    // Lightweight functional coverage
    cover (cout);                // carry-out observed
    cover (!cout);               // no carry-out
    cover (sum == 4'h0);         // zero sum
    cover (sum == 4'hF);         // max sum (no carry)
    cover ({a,b,cin} == 9'b0);   // all zeros
    cover ({a,b,cin} == {4'hF,4'hF,1'b1}); // overflow corner
  end
endmodule

// Bind into the DUT
bind ripple_adder ripple_adder_sva i_ripple_adder_sva (.a(a), .b(b), .cin(cin), .sum(sum), .cout(cout));