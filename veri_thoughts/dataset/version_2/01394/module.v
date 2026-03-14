module parity_checker (
  input [3:0] data,
  output reg parity
);

  always @* begin
    parity = ^data; // XOR all bits in data
  end

endmodule