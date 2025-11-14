module comparator (
    input [3:0] A,
    input [3:0] B,
    input clk,
    output EQ,
    output GT,
    output LT
);

reg [3:0] A_reg;
reg [3:0] B_reg;
reg [1:0] stage;

assign EQ = (A_reg == B_reg);
assign GT = (A_reg > B_reg);
assign LT = (A_reg < B_reg);

always @(*) begin
    case(stage)
        0: begin
            A_reg = A;
            B_reg = B;
        end
        1: begin
            A_reg = A_reg;
            B_reg = B_reg;
        end
    endcase
end

always @(posedge clk) begin
    if (stage == 1) begin
        stage <= 0;
    end else begin
        stage <= 1;
    end
end

endmodule