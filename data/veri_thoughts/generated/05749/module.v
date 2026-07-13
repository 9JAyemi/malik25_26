module arithmetic_operations (
    input [7:0] A,
    input [7:0] B,
    input [2:0] ctrl,
    output reg [7:0] out
);

    always @(*) begin
        case(ctrl)
            3'b000: out = A & B; // A AND B
            3'b001: out = A | B; // A OR B
            3'b010: out = A ^ B; // A XOR B
            3'b011: out = A + B; // A + B
            3'b100: out = A - B; // A - B
            3'b101: out = A * B; // A * B
            3'b110: out = A / B; // A / B
            3'b111: out = A % B; // A % B
        endcase
    end

endmodule