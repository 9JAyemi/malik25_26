
module half_full_adder (
  input a,
  input b,
  input cin,
  output s,
  output cout
);

  wire ha_s, ha_c;
  wire fa_s, fa_c1, fa_c2;

  assign ha_s = a ^ b;
  assign ha_c = a & b;
  
  assign fa_s = ha_s ^ cin;
  assign fa_c1 = ha_s & cin;
  assign fa_c2 = ha_c;

  assign s = fa_s;
  assign cout = fa_c1 | fa_c2;
  
endmodule