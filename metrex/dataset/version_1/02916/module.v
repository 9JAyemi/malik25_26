
module adder (
    input [7:0] data1,
    input [7:0] data2,
    output reg [7:0] out
);

reg [7:0] carry;

always @(*) begin
    carry = (data1 + data2 > 255) ? 1 : 0;
    out = data1 + data2 + carry;
end

endmodule