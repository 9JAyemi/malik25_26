
module binary_priority_decoder #(
  parameter n = 4 // number of binary signals
)(
  input [n-1:0] in,
  input [n-1:0] priority_bits,
  output reg out
);


wire [n-1:0] priority_encoded;
wire [n-1:0] priority_sorted;
wire [n-1:0] priority_mask;
wire [n-1:0] priority_masked;

assign priority_encoded = ~(in ^ priority_bits);
assign priority_sorted = {priority_encoded[n-1], priority_encoded[n-2:0]};
assign priority_mask = {priority_sorted[n-1] & priority_sorted[n-2:0], priority_sorted[n-2] & priority_sorted[n-3:0], priority_sorted[n-3] & priority_sorted[n-4:0], priority_sorted[n-4]};
assign priority_masked = priority_encoded & priority_mask;

always @(*) begin
  case (priority_masked)
    4'b0000: out = 1'b0;
    4'b0001: out = 1'b1;
    4'b0010: out = 1'b1;
    4'b0100: out = 1'b1;
    4'b1000: out = 1'b1;
    default: out = 1'bx;
  endcase
end

endmodule
