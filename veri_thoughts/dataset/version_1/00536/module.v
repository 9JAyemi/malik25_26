
module adder_4bit(
    input [3:0] A,
    input [3:0] B,
    input Cin,
    input Clk,
    output [3:0] S,
    output Cout
);

reg [4:0] sum; // Changed the size of sum to 5 bits to accommodate the carry-out

always @(posedge Clk) begin
    if (Cin) begin
        sum <= A + B + 1;
    end else begin
        sum <= A + B;
    end
end

assign S = sum[3:0];
assign Cout = sum[4];

endmodule