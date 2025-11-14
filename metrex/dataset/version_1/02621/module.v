module barrel_shifter (
    input [3:0] A,
    input [3:0] B,
    output reg [3:0] result
);

    always @(*) begin
        if (B >= 0) begin
            result = A << B;
        end else begin
            result = A >> $signed(B);
        end
    end

endmodule