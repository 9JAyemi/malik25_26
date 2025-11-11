module half_subtractor (
  input a,
  input b,
  output diff,
  output bout
);
  assign diff = a ^ b;
  assign bout = a & ~b;
endmodule

module full_subtractor (
  input a,
  input b,
  input bin,
  output diff,
  output bout
);
  wire temp_diff1, temp_diff2, temp_bout1, temp_bout2;
  half_subtractor hs1(.a(a), .b(b), .diff(temp_diff1), .bout(temp_bout1));
  half_subtractor hs2(.a(temp_diff1), .b(bin), .diff(diff), .bout(temp_bout2));
  assign bout = temp_bout1 | temp_bout2;
endmodule