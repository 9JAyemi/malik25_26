
module twos_complement (
    input [3:0] in,
    output reg [4:0] out
);

reg [3:0] in_reg;
reg [3:0] neg_in_reg;

always @(in) begin
    in_reg = in;
    neg_in_reg = ~in_reg + 1'b1;
end

always @(*) begin
    if (in_reg[3]) begin
        out = {1'b1, ~in_reg + 1'b1};
    end else begin
        out = {1'b0, in_reg};
    end
end

endmodule
