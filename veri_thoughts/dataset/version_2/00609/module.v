
module top_module (
    input [3:0] A,
    input [3:0] B,
    input enable,
    output reg [3:0] q
);

  wire greater_or_equal;
  magnitude_comparator comparator(A, B, greater_or_equal);

  always @ (greater_or_equal, enable) begin
    if (greater_or_equal & enable) begin
      q <= A;
    end else begin
      q <= B;
    end
  end

endmodule

module magnitude_comparator (
    input [3:0] A,
    input [3:0] B,
    output reg greater_or_equal
);

  always @ (A, B) begin
    if (A >= B) begin
      greater_or_equal <= 1;
    end else begin
      greater_or_equal <= 0;
    end
  end

endmodule
