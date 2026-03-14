
module compare_op (
    input [3:0] A,
    input [3:0] B,
    output reg [3:0] Y
);

    always @(*) begin
        if (A > B)
            Y = A - B;
        else
            Y = B - A;
    end

endmodule