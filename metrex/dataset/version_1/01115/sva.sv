// SVA binders for ripple_carry_adder system

// Full-adder checks
module fa_sva (
  input logic a, b, cin,
  input logic sum, cout
);
  default clocking cb @(*) endclocking

  // Knownness: known inputs imply known outputs
  a_known:  assert property ((!$isunknown({a,b,cin})) |-> ##0 !$isunknown({sum,cout}));

  // Functional correctness
  a_func:   assert property (##0 {cout,sum} == a + b + cin);

  // Key coverage
  c_gen:    cover property ( (a & b) & ~cin );      // carry generate
  c_prop:   cover property ( (a ^ b) &  cin );      // carry propagate
endmodule

bind full_adder fa_sva u_fa_sva (.a(a), .b(b), .cin(cin), .sum(sum), .cout(cout));


// Ripple-carry-adder checks (includes internal carries)
module rca_sva (
  input  logic [3:0] a, b, sum,
  input  logic       cout, overflow,
  input  logic [4:0] c
);
  default clocking cb @(*) endclocking

  // Knownness: known inputs imply known outputs
  a_known:  assert property ((!$isunknown({a,b})) |-> ##0 !$isunknown({sum,cout,overflow}));

  // Carry-in fixed
  a_c0:     assert property (##0 c[0] == 1'b0);

  // Bit-slice FA equations
  genvar i;
  generate
    for (i=0;i<4;i++) begin : g
      a_sum_i: assert property (##0 (sum[i] == (a[i]^b[i]^c[i])));
      a_cout_i:assert property (##0 (c[i+1] == ((a[i]&b[i])|(a[i]&c[i])|(b[i]&c[i]))));
    end
  endgenerate

  // Overall arithmetic
  a_add:    assert property (##0 {cout,sum} == a + b);

  // Overflow equivalences
  a_ovf_exp:assert property (##0 overflow == ((a[3]&b[3]&~sum[3]) | (~a[3]&~b[3]&sum[3])));
  a_ovf_xor:assert property (##0 overflow == (c[4] ^ c[3]));

  // Key coverage
  c_cout:   cover property ( cout );
  c_ovf_pos:cover property ( overflow & ~a[3] & ~b[3] &  sum[3] ); // + + -> -
  c_ovf_neg:cover property ( overflow &  a[3] &  b[3] & ~sum[3] ); // - - -> +
  c_zero:   cover property ( (sum==4'd0) & ~cout );
endmodule

bind ripple_carry_adder rca_sva u_rca_sva (.a(a),.b(b),.sum(sum),.cout(cout),.overflow(overflow),.c(c));


// Greater-than-9 checks
module gto9_sva (
  input logic [3:0] sum,
  input logic       greater_than_9
);
  default clocking cb @(*) endclocking

  a_known:  assert property ((!$isunknown(sum)) |-> ##0 !$isunknown(greater_than_9));
  a_func:   assert property (##0 greater_than_9 == (sum > 4'd9));

  // Threshold coverage
  c_eq9:    cover property ( (sum==4'd9)  & ~greater_than_9 );
  c_eq10:   cover property ( (sum==4'd10) &  greater_than_9 );
  c_max:    cover property ( (sum==4'd15) &  greater_than_9 );
  c_zero:   cover property ( (sum==4'd0)  & ~greater_than_9 );
endmodule

bind greater_than_9 gto9_sva u_gto9_sva (.sum(sum), .greater_than_9(greater_than_9));