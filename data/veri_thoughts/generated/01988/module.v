module signed_mag_comp (
    input signed [3:0] A,
    input signed [3:0] B,
    output reg EQ,
    output reg GT
);

    always @(*) begin
        if (A == B) begin
            EQ = 1;
            GT = 0;
        end else if (A > B) begin
            EQ = 0;
            GT = 1;
        end else begin
            EQ = 0;
            GT = 0;
        end
    end

endmodule