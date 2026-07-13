
module multiplier_4bit (
    input [3:0] A,
    input [3:0] B,
    output reg [7:0] P
);

reg [7:0] temp;

always @(*) begin
    temp = A * B;
    P = temp;
end

endmodule