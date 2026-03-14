module addsub32 (
    input [31:0] A,
    input [31:0] B,
    input op,
    output reg [31:0] R
);

always @(*) begin
    if (op == 0) // addition
        R = A + B;
    else // subtraction
        R = A - B;
end

endmodule

