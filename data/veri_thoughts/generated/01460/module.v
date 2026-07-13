module Comparator (
  input [n-1:0] a,
  input [n-1:0] b,
  input [1:0] ctrl,
  output reg out
);

parameter n = 8; // number of bits in input numbers

reg signed [n-1:0] a_signed, b_signed;

// Sign extension for signed numbers
always @(*) begin
  if (ctrl == 2'b01) begin // a > b
    if (a[n-1] == 1) // a is negative
      a_signed = {{n-1{1'b1}}, a};
    else
      a_signed = {n-1'b0, a};
    
    if (b[n-1] == 1) // b is negative
      b_signed = {{n-1{1'b1}}, b};
    else
      b_signed = {n-1'b0, b};
  end
  else if (ctrl == 2'b10) begin // a < b
    if (a[n-1] == 1) // a is negative
      a_signed = {{n-1{1'b1}}, a};
    else
      a_signed = {n-1'b0, a};
    
    if (b[n-1] == 1) // b is negative
      b_signed = {{n-1{1'b1}}, b};
    else
      b_signed = {n-1'b0, b};
  end
end

// Comparison logic
always @(*) begin
  case (ctrl)
    2'b00: out = (a == b);
    2'b01: out = (a_signed > b_signed);
    2'b10: out = (a_signed < b_signed);
    default: out = 1'b0;
  endcase
end

endmodule