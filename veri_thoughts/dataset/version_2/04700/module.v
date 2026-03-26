module barrel_shifter (
    input [3:0] A,
    input [1:0] SHIFT,
    output reg [3:0] Y
);

    always @(*) begin
        case(SHIFT)
            2'b00: Y = A; // No shift
            2'b01: Y = {A[2:0], 1'b0}; // Left shift
            2'b10: Y = {1'b0, A[3:1]}; // Right shift
            2'b11: Y = {A[1:0], A[3:2]}; // Left shift by 2
        endcase
    end

endmodule