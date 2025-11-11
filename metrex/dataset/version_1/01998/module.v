
module ripple_carry_adder(
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output [3:0] S,
    output Cout
);

wire [3:0] sum;
wire [3:0] carry;

assign sum = A ^ B ^ Cin;
assign carry[0] = (A & B) | (Cin & (A ^ B));

assign S = sum;
assign Cout = carry[3];

genvar i;
generate
    for(i=1; i<4; i=i+1) begin : carry_propagation
        assign carry[i] = carry[i-1] & sum[i-1];
    end
endgenerate

endmodule