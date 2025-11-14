// SVA for four_bit_adder and full_adder
// Focused, concise, high-quality checks and coverage

// Checker for the 1-bit full adder
module full_adder_sva(input a, b, cin, s, cout);
  // Functional correctness (guarded against X on inputs)
  always_comb begin
    if (!$isunknown({a,b,cin})) begin
      assert (s    == (a ^ b ^ cin)) else $error("full_adder: s mismatch");
      assert (cout == ((a & b) | (cin & (a ^ b)))) else $error("full_adder: cout mismatch");
      assert (!$isunknown({s,cout})) else $error("full_adder: X/Z on outputs with known inputs");
    end
  end

  // Exhaustive input coverage (all 8 combinations)
  generate
    genvar v;
    for (v=0; v<8; v++) begin : fa_cov_all
      localparam [2:0] pat = v[2:0];
      cover property (@(*) {a,b,cin} == pat);
    end
  endgenerate

  // Output toggle coverage
  cover property (@(*) s==0);
  cover property (@(*) s==1);
  cover property (@(*) cout==0);
  cover property (@(*) cout==1);
endmodule

bind full_adder full_adder_sva fa_chk (.a(a), .b(b), .cin(cin), .s(s), .cout(cout));


// Checker for the 4-bit ripple-carry adder
module four_bit_adder_sva(
  input  [3:0] a, b,
  input        cin,
  input  [3:0] s,
  input        cout,
  // internal nets
  input  [3:0] sum,
  input        cout0, cout1, cout2
);
  // Functional correctness vs mathematical spec
  always_comb begin
    if (!$isunknown({a,b,cin})) begin
      assert ({cout,s} == a + b + cin) else $error("four_bit_adder: {cout,s} != a+b+cin");
      assert (s == sum) else $error("four_bit_adder: s != internal sum");
      // Stage-by-stage checks
      assert (sum[0] == (a[0]^b[0]^cin))                           else $error("Bit0 sum mismatch");
      assert (cout0   == ((a[0]&b[0]) | (cin   & (a[0]^b[0]))))     else $error("Bit0 carry mismatch");

      assert (sum[1] == (a[1]^b[1]^cout0))                          else $error("Bit1 sum mismatch");
      assert (cout1   == ((a[1]&b[1]) | (cout0 & (a[1]^b[1]))))     else $error("Bit1 carry mismatch");

      assert (sum[2] == (a[2]^b[2]^cout1))                          else $error("Bit2 sum mismatch");
      assert (cout2   == ((a[2]&b[2]) | (cout1 & (a[2]^b[2]))))     else $error("Bit2 carry mismatch");

      assert (sum[3] == (a[3]^b[3]^cout2))                          else $error("Bit3 sum mismatch");
      assert (cout    == ((a[3]&b[3]) | (cout2 & (a[3]^b[3]))))     else $error("Bit3 carry mismatch");

      assert (!$isunknown({s,cout,sum,cout0,cout1,cout2})) else $error("X/Z on outputs/internal with known inputs");
    end
  end

  // High-value coverage scenarios
  // No-carry, carry-in only, overflow, zero case, maximum overflow, full propagate chain
  cover property (@(*) (cin==0 && cout==0));
  cover property (@(*) (cin==1 && cout==0));
  cover property (@(*) (cout==1));
  cover property (@(*) (a==4'h0 && b==4'h0 && cin==1'b0 && s==4'h0 && cout==1'b0));
  cover property (@(*) (a==4'hF && b==4'hF && cin==1'b1 && s==4'hF && cout==1'b1));
  cover property (@(*) ((a^b)==4'hF && cin==1'b1 && cout==1'b1)); // full propagate chain

  // Ensure each sum bit toggles to 0 and 1 across sim
  generate
    genvar i;
    for (i=0; i<4; i++) begin : sum_bit_cov
      cover property (@(*) s[i]==0);
      cover property (@(*) s[i]==1);
    end
  endgenerate

  // Ensure each internal carry takes 0 and 1 values
  wire [2:0] c = {cout2, cout1, cout0};
  generate
    genvar j;
    for (j=0; j<3; j++) begin : carry_cov
      cover property (@(*) c[j]==0);
      cover property (@(*) c[j]==1);
    end
  endgenerate
endmodule

bind four_bit_adder four_bit_adder_sva fba_chk (
  .a(a), .b(b), .cin(cin), .s(s), .cout(cout),
  .sum(sum), .cout0(cout0), .cout1(cout1), .cout2(cout2)
);