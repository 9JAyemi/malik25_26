
module nor_using_nand_pipeline(
    input a,
    input b,
    output out,
    input clk
);

reg a_reg, b_reg;
wire nand1_out, nand2_out, nand3_out;

// Pipeline stage 1
assign nand1_out = ~(a & b);
always @(posedge clk) begin
    a_reg <= a;
    b_reg <= b;
end

// Pipeline stage 2
assign nand2_out = ~(a_reg & nand1_out);

// Pipeline stage 3
assign nand3_out = ~(b_reg & nand2_out);

// Output stage
assign out = nand3_out;

endmodule