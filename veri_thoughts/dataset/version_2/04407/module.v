
module keypad_scanner (
    input clk,
    input [3:0] col,
    output reg [3:0] row
);

reg [3:0] row_pipe1, row_pipe2, row_pipe3;

always @(posedge clk) begin
    row_pipe1 <= row;
    row_pipe2 <= row_pipe1;
    row_pipe3 <= row_pipe2;
    
    case (col)
        4'b1110: row <= 4'b1110;
        4'b1101: row <= 4'b1101;
        4'b1011: row <= 4'b1011;
        4'b0111: row <= 4'b0111;
        default: row <= 4'b0000;
    endcase
end

endmodule