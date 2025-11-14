
module ripple_carry_adder (
    input [3:0] A,
    input [3:0] B,
    output [3:0] S,
    output C
);

reg carry_out;
reg [3:0] carry_in; 

always @* begin
    {carry_out, S[0]} = A[0] + B[0];
    {carry_in[1], S[1]} = A[1] + B[1] + carry_out;
    {carry_in[2], S[2]} = A[2] + B[2] + carry_in[1];
    {C, S[3]} = A[3] + B[3] + carry_in[2];
end

endmodule