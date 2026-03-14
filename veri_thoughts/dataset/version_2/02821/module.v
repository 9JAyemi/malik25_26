module magnitude_comparator (
    input [3:0] A,
    input [3:0] B,
    output reg GT,
    output reg EQ
);

always @(*) begin
    if (A > B) begin
        GT = 1;
        EQ = 0;
    end
    else if (A == B) begin
        GT = 0;
        EQ = 1;
    end
    else begin
        GT = 0;
        EQ = 0;
    end
end

endmodule