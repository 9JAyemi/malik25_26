module PE_ctrl(
    input [10:0] ctrl,
    output reg [3:0] op,
    output reg [31:0] width
);

always @(*) begin
    case(ctrl[5:0])
        6'b000000: begin
            op = 4'b0000;
        end
        6'b000001: begin
            op = 4'b0001;
        end
        6'b000010: begin
            op = 4'b0010;
        end
        6'b000011: begin
            op = 4'b0011;
        end
        6'b000100: begin
            op = 4'b0100;
        end
        6'b000101: begin
            op = 4'b0101;
        end
        6'b000110: begin
            op = 4'b0110;
        end
        6'b000111: begin
            op = 4'b0111;
        end
        6'b001000: begin
            op = 4'b1000;
        end
        6'b001001: begin
            op = 4'b1001;
        end
        6'b001010: begin
            op = 4'b1010;
        end
        6'b001011: begin
            op = 4'b1011;
        end
        6'b001100: begin
            op = 4'b1100;
        end
        6'b001101: begin
            op = 4'b1101;
        end
        6'b001110: begin
            op = 4'b1110;
        end
        6'b001111: begin
            op = 4'b1111;
        end
        6'b010000: begin
            op = 4'b1111;
        end
        6'b010001: begin
            op = 4'b0011;
        end
        6'b010010: begin
            op = 4'b0100;
        end
        6'b010011: begin
            op = 4'b1111;
        end
        6'b010100: begin
            op = 4'b0111;
        end
        6'b010101: begin
            op = 4'b1001;
        end
        6'b010110: begin
            op = 4'b1011;
        end
        6'b010111: begin
            op = 4'b1101;
        end
        6'b011000: begin
            op = 4'b0111;
        end
        6'b011001: begin
            op = 4'b1001;
        end
        6'b011010: begin
            op = 4'b1111;
        end
        6'b011011: begin
            op = 4'b0011;
        end
        6'b011100: begin
            op = 4'b0100;
        end
        6'b011101: begin
            op = 4'b1010;
        end
        6'b011110: begin
            op = 4'b1111;
        end
        6'b011111: begin
            op = 4'b1111;
        end
        default: begin
            op = 4'b0000;
        end
    endcase
    width = 2 ** ctrl[10:6];
end

endmodule