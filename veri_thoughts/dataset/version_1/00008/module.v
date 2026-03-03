module calculator(
    input [7:0] A,
    input [7:0] B,
    input [1:0] op,
    output reg [7:0] Y
);

    always @* begin
        case(op)
            2'b00: Y = A + B;
            2'b01: Y = A - B;
            2'b10: Y = A * B;
            2'b11: Y = A / B;
        endcase
    end

endmodule