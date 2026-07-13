module four_bit_adder(
    input [3:0] A,
    input [3:0] B,
    output reg [3:0] S,
    output C
);

    wire [3:0] sum;
    wire carry;

    assign sum = A + B;
    assign C = (A[3] & B[3]) | ((A[3] | B[3]) & ~sum[3]);

    always @* begin
        if (C) begin
            S = sum + 4'b1;
        end else begin
            S = sum;
        end
    end

endmodule