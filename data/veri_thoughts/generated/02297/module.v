
module nor4(
  input a,
  input b,
  input c,
  input d,
  output y
);

  wire ab, cd;

  nor2 NOR2_0 (
    .a(a),
    .b(b),
    .y(ab)
  );

  nor2 NOR2_1 (
    .a(c),
    .b(d),
    .y(cd)
  );

  nor2 NOR2_2 (
    .a(ab),
    .b(cd),
    .y(y)
  );

endmodule

module nor2(
  input a,
  input b,
  output y
);

  assign y = ~(a | b);

endmodule
