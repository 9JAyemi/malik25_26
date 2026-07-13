
module adder(
    input [3:0] A,
    input [3:0] B,
    output reg [3:0] S,
    output reg C
);

always @* begin
    {C, S} = A + B;
end

endmodule