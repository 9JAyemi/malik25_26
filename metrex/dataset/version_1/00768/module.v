module add_sub (
    input [3:0] A,
    input [3:0] B,
    input SUBTRACT,
    output reg [3:0] SUM,
    output reg OVERFLOW
);

always @(*) begin
    if (SUBTRACT == 1) begin
        SUM <= A - B;
        if (A < B) begin
            OVERFLOW <= 1;
        end else begin
            OVERFLOW <= 0;
        end
    end else begin
        SUM <= A + B;
        if (SUM > 15) begin
            OVERFLOW <= 1;
        end else begin
            OVERFLOW <= 0;
        end
    end
end

endmodule