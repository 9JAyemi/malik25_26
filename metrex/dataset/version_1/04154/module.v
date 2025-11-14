
module adder_8bit (
    input [7:0] A,
    input [7:0] B,
    output reg [7:0] S,
    output reg C_out
);

    wire [7:0] c;

    always @* begin
        {C_out, c[7], S[7]} = A[7] + B[7];
        {c[6], S[6]} = c[7] + A[6] + B[6];
        {c[5], S[5]} = c[6] + A[5] + B[5];
        {c[4], S[4]} = c[5] + A[4] + B[4];
        {c[3], S[3]} = c[4] + A[3] + B[3];
        {c[2], S[2]} = c[3] + A[2] + B[2];
        {c[1], S[1]} = c[2] + A[1] + B[1];
        {c[0], S[0]} = c[1] + A[0] + B[0];
    end

endmodule