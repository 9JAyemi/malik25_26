
module barrel_shifter (
    input [3:0] A,
    input [3:0] B,
    output [3:0] result
);

reg [3:0] stage1_out;
reg [3:0] stage2_out;

wire [3:0] abs_B;

assign abs_B = (B[3] == 1'b1) ? ~B + 1'b1 : B;

always @(*) begin
    stage1_out = (B[3] == 1'b0) ? (A << B) : (A >> abs_B);
end

always @(*) begin
    stage2_out = stage1_out;
end

assign result = stage2_out;

endmodule
