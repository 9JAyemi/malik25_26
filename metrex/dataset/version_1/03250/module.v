
module barrel_shifter (
    input [15:0] A, // 16-bit input
    input [3:0] B, // 4-bit shift amount
    output reg [15:0] Y // 16-bit output
);

reg [15:0] stage1_out;
reg [15:0] stage2_out;
reg [15:0] stage3_out;

always @(*) begin
    case (B)
        4'b0000: begin // No shift
            Y = A;
        end
        4'b0001: begin // Shift right by 1 bit
            stage1_out = {16{A[15]}};
            stage2_out = stage1_out;
            stage3_out = stage2_out;
            Y = stage3_out;
        end
        4'b0010: begin // Shift right by 2 bits
            stage1_out = {16{A[15]}};
            stage2_out = stage1_out;
            stage3_out = stage2_out;
            Y = stage3_out;
        end
        4'b0011: begin // Shift right by 3 bits
            stage1_out = {16{A[15]}};
            stage2_out = stage1_out;
            stage3_out = stage2_out;
            Y = stage3_out;
        end
        4'b0100: begin // Shift right by 4 bits
            stage1_out = {A[11:0], A[15:12]};
            stage2_out = stage1_out;
            stage3_out = stage2_out;
            Y = stage3_out;
        end
        4'b0101: begin // Shift right by 5 bits
            stage1_out = {A[10:0], A[15:11]};
            stage2_out = stage1_out;
            stage3_out = stage2_out;
            Y = stage3_out;
        end
        4'b0110: begin // Shift right by 6 bits
            stage1_out = {A[9:0], A[15:10]};
            stage2_out = stage1_out;
            stage3_out = stage2_out;
            Y = stage3_out;
        end
        4'b0111: begin // Shift right by 7 bits
            stage1_out = {A[8:0], A[15:9]};
            stage2_out = stage1_out;
            stage3_out = stage2_out;
            Y = stage3_out;
        end
        4'b1000: begin // Shift right by 8 bits
            stage1_out = {A[7:0], A[15:8]};
            stage2_out = stage1_out;
            stage3_out = stage2_out;
            Y = stage3_out;
        end
        4'b1001: begin // Shift right by 9 bits
            stage1_out = {A[6:0], A[15:7]};
            stage2_out = stage1_out;
            stage3_out = stage2_out;
            Y = stage3_out;
        end
        4'b1010: begin // Shift right by 10 bits
            stage1_out = {A[5:0], A[15:6]};
            stage2_out = stage1_out;
            stage3_out = stage2_out;
            Y = stage3_out;
        end
        4'b1011: begin // Shift right by 11 bits
            stage1_out = {A[4:0], A[15:5]};
            stage2_out = stage1_out;
            stage3_out = stage2_out;
            Y = stage3_out;
        end
        4'b1100: begin // Shift right by 12 bits
            stage1_out = {A[3:0], A[15:4]};
            stage2_out = stage1_out;
            stage3_out = stage2_out;
            Y = stage3_out;
        end
        4'b1101: begin // Shift right by 13 bits
            stage1_out = {A[2:0], A[15:3]};
            stage2_out = stage1_out;
            stage3_out = stage2_out;
            Y = stage3_out;
        end
        4'b1110: begin // Shift right by 14 bits
            stage1_out = {A[1:0], A[15:2]};
            stage2_out = stage1_out;
            stage3_out = stage2_out;
            Y = stage3_out;
        end
        4'b1111: begin // Shift right by 15 bits
            stage1_out = {A[0], A[15:1]};
            stage2_out = stage1_out;
            stage3_out = stage2_out;
            Y = stage3_out;
        end
    endcase
end

endmodule