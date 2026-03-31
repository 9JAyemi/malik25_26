
module comparator (
    input [3:0] in0,
    input [3:0] in1,
    output reg [1:0] result
);

reg [3:0] in0_reg;
reg [3:0] in1_reg;


always @(in0, in1) begin
    in0_reg <= in0;
    in1_reg <= in1;

    if (in0_reg > in1_reg) begin
        result <= 2'b01;
    end else if (in0_reg < in1_reg) begin
        result <= 2'b10;
    end else begin
        result <= 2'b00;
    end
end

endmodule
