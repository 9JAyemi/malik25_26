
module bitwise_or (
    input [3:0] a,
    input [3:0] b,
    output reg [3:0] out
);

// Stage 1
wire [3:0] stage1_out;
assign stage1_out = a | b;

// Stage 2
always @(*) begin
    out <= stage1_out;
end

endmodule