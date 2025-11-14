module trig_functions (
  input x,
  output reg sin_out,
  output reg cos_out,
  output reg tan_out
);

  reg [31:0] fact;
  reg [31:0] x_pow;
  reg [31:0] term;
  reg [31:0] sign;
  reg [31:0] i;

  always @(*) begin
    fact = 1;
    x_pow = x;
    term = x;
    sign = 1;
    sin_out = x;
    cos_out = 1;
    tan_out = sin_out / cos_out;

    for (i = 3; i <= 15; i = i + 2) begin
      fact = fact * i * (i - 1);
      x_pow = x_pow * x * x;
      sign = -1 * sign;
      term = sign * x_pow / fact;
      sin_out = sin_out + term;
      cos_out = cos_out + term * term;
      tan_out = sin_out / cos_out;
    end

    if (x == 0) begin
      sin_out = 0;
      cos_out = 1;
      tan_out = 0;
    end

    if (cos_out == 0) begin
      tan_out = 1;
    end
  end

endmodule