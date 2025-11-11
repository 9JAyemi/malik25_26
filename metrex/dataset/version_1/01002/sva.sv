// SVA for ripple_adder_32 and full_adder
// Bind these to the DUTs; assertions are concurrent and settle with ##0 after any input change.

module ripple_adder_32_sva;
  // End-to-end correctness
  assert property (@(a or b or cin) 1'b1 |-> ##0 {cout, sum} == a + b + cin);

  // Bit 0 equations
  assert property (@(a[0] or b[0] or cin)
                   1'b1 |-> ##0 (s[0] == (a[0]^b[0]^cin)) &&
                                   (c[0] == ((a[0]&b[0])|(a[0]&cin)|(b[0]&cin))));

  // Bits 1..30 equations
  genvar i;
  generate
    for (i=1; i<31; i++) begin : g_bits
      assert property (@(a[i] or b[i] or c[i-1])
                       1'b1 |-> ##0 (s[i] == (a[i]^b[i]^c[i-1])) &&
                                       (c[i] == ((a[i]&b[i])|(a[i]&c[i-1])|(b[i]&c[i-1]))));
    end
  endgenerate

  // MSB carry-out
  assert property (@(a[31] or b[31] or c[30])
                   1'b1 |-> ##0 cout == ((a[31]&b[31])|(a[31]&c[30])|(b[31]&c[30])));

  // sum mirrors internal s
  assert property (@(s) 1'b1 |-> ##0 sum == s);

  // No X/Z on outputs when inputs are known (ignore unused c[31])
  assert property (@(a or b or cin) !$isunknown({a,b,cin}) |-> ##0
                   !$isunknown({sum,cout,s,c[30:0]}));

  // Functional coverage
  cover property (@(a or b or cin) ##0 (cin==1'b0));
  cover property (@(a or b or cin) ##0 (cin==1'b1));
  cover property (@(a or b or cin) ##0 (cout==1'b1));
  cover property (@(a or b or cin) ##0 (sum==32'h0000_0000));
  cover property (@(a or b or cin) ##0 ({cout,sum}==33'h1_0000_0000)); // unsigned overflow
  cover property (@(a or b or cin) ##0 ((a[31]==b[31]) && (sum[31]!=a[31]))); // signed overflow
  cover property (@(a or b or cin) ##0 (a==32'hFFFF_FFFF && b==32'h0000_0001 && cin==1'b0)); // full ripple
endmodule

bind ripple_adder_32 ripple_adder_32_sva;


// SVA for leaf full_adder (truth and no-X)
module full_adder_sva;
  assert property (@(a or b or cin) 1'b1 |-> ##0 {cout,sum} == a + b + cin);
  assert property (@(a or b or cin) 1'b1 |-> ##0 (sum == (a^b^cin)) &&
                                              (cout == ((a&b)|(a&cin)|(b&cin))));
  assert property (@(a or b or cin) !$isunknown({a,b,cin}) |-> ##0 !$isunknown({sum,cout}));

  // Cover all input combinations
  cover property (@(a or b or cin) ##0 {a,b,cin} == 3'b000);
  cover property (@(a or b or cin) ##0 {a,b,cin} == 3'b001);
  cover property (@(a or b or cin) ##0 {a,b,cin} == 3'b010);
  cover property (@(a or b or cin) ##0 {a,b,cin} == 3'b011);
  cover property (@(a or b or cin) ##0 {a,b,cin} == 3'b100);
  cover property (@(a or b or cin) ##0 {a,b,cin} == 3'b101);
  cover property (@(a or b or cin) ##0 {a,b,cin} == 3'b110);
  cover property (@(a or b or cin) ##0 {a,b,cin} == 3'b111);
endmodule

bind full_adder full_adder_sva;