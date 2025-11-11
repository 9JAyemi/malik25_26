
module adder (
    input [3:0] A,
    input [3:0] B,
    input sel,
    output reg [3:0] C
);

    wire [3:0] sum;
    wire carry;

    assign sum = A + B;
    assign carry = (A[3] & B[3]) | (A[3] & ~sum[3]) | (B[3] & ~sum[3]);

    always @ (*) begin
        C = sel ? ~{carry, sum} : {carry, sum};
    end

endmodule