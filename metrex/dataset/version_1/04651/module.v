
module comparator (
    input [2:0] A,
    input [2:0] B,
    input [2:0] C,
    output reg [1:0] Y
);

    wire Y1_0, Y1_1, Y2_0, Y2_1;

    and (Y1_0, A[2], A[1], C[0]);
    and (Y2_0, B[2], B[1], C[1]);
    and (Y1_1, C[2], B[0], Y1_0);
    and (Y2_1, A[0], Y2_0, Y1_0);

    always @(*) begin
        if (Y1_0 == 1 && Y2_0 == 1 && Y1_1 == 0 && Y2_1 == 0) begin
            Y = 2'b00;
        end else if (Y1_0 == 1 && Y2_0 == 1 && Y1_1 == 0 && Y2_1 == 1) begin
            Y = 2'b01;
        end else if (Y1_0 == 1 && Y2_0 == 1 && Y1_1 == 1 && Y2_1 == 0) begin
            Y = 2'b10;
        end else begin
            Y = 2'b11;
        end
    end

endmodule