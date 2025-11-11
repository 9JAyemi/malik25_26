module comparator_4bit (
    input [3:0] in_a,
    input [3:0] in_b,
    input clk,
    output eq,
    output gt,
    output lt
);

reg [3:0] a_reg, b_reg;
reg eq_reg, gt_reg, lt_reg;

always @(posedge clk) begin
    a_reg <= in_a;
    b_reg <= in_b;
end

always @(posedge clk) begin
    if (a_reg == b_reg) begin
        eq_reg <= 1'b1;
        gt_reg <= 1'b0;
        lt_reg <= 1'b0;
    end else if (a_reg > b_reg) begin
        eq_reg <= 1'b0;
        gt_reg <= 1'b1;
        lt_reg <= 1'b0;
    end else begin
        eq_reg <= 1'b0;
        gt_reg <= 1'b0;
        lt_reg <= 1'b1;
    end
end

assign eq = eq_reg;
assign gt = gt_reg;
assign lt = lt_reg;

endmodule