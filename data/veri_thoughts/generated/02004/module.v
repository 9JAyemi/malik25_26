module binary_comparator (
    input [7:0] A,
    input [7:0] B,
    output reg EQ,
    output reg LT,
    output reg GT
);

    always @(*) begin
        if (A == B) begin
            EQ = 1;
            LT = 0;
            GT = 0;
        end else if (A < B) begin
            EQ = 0;
            LT = 1;
            GT = 0;
        end else begin
            EQ = 0;
            LT = 0;
            GT = 1;
        end
    end

endmodule