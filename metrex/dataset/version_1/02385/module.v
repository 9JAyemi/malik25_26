module mag_comp(
    input [3:0] A,
    input [3:0] B,
    output EQ,
    output GT,
    output LT
);

    reg EQ, GT, LT;

    always @(*) begin
        case(A > B)
            1'b0: begin
                EQ = (A == B);
                GT = 1'b0;
                LT = 1'b1;
            end
            1'b1: begin
                EQ = 1'b0;
                GT = 1'b1;
                LT = 1'b0;
            end
        endcase
    end

endmodule