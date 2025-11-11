
module multiplier (
  input [n-1:0] A,
  input [n-1:0] B,
  input ctrl,
  output [2*n-1:0] P
);

parameter n = 8; // number of bits in the input numbers

integer i;

reg [2*n-1:0] temp;

assign P = temp;

always @(*) begin
  if (ctrl == 0) begin // unsigned multiplication
    temp = 0; // initialize P to 0
    for (i = 0; i < n; i = i + 1) begin
      if (B[i] == 1) begin
        temp = temp + (A << i);
      end
    end
  end
  else begin // signed multiplication
    temp = 0; // initialize P to 0
    if (A[n-1] == 1) begin // sign extend A
      temp = {{(n){1'b1}}, A};
    end
    else begin
      temp = A;
    end
    if (B[n-1] == 1) begin // sign extend B
      temp = temp + ({{(n){1'b1}}, B} << n);
    end
    else begin
      temp = temp + (B << n);
    end
    // Booth's algorithm for signed multiplication
    for (i = 0; i < n-1; i = i + 1) begin
      if (B[i] == 1 && B[i+1] == 0) begin // 01 pattern
        temp = temp - (A << (i+1));
      end
      else if (B[i] == 0 && B[i+1] == 1) begin // 10 pattern
        temp = temp + (A << (i+1));
      end
    end
  end
end

endmodule