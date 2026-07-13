
module parity_check (
  input [7:0] data,
  output reg parity_error
);
  wire [7:0] xor_result;

  assign xor_result = ^data;

  always @(*) begin
    parity_error <= (xor_result == 1);
  end
endmodule
