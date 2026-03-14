module four_bit_comparator (
  input [3:0] a,
  input [3:0] b,
  output reg eq,
  output reg gt,
  output reg lt
);

  // Check for equality
  always @* begin
    eq = (a == b);
  end

  // Check for greater than
  always @* begin
    if (a > b)
      gt = 1;
    else
      gt = 0;
  end

  // Check for less than
  always @* begin
    if (a < b)
      lt = 1;
    else
      lt = 0;
  end

endmodule