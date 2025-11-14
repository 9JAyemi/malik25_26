module booth_multiplier (
    input signed [31:0] a,
    input signed [31:0] b,
    input clk,
    output signed [63:0] product
);

reg signed [63:0] product_reg;
reg signed [31:0] a_reg;
reg signed [31:0] b_reg;
reg signed [31:0] m_reg;
reg signed [31:0] ac_reg;
reg signed [1:0] count_reg;

always @(*) begin
    product_reg = a_reg * b_reg;
    a_reg = a;
    b_reg = b;
    m_reg = {b_reg[31], b_reg};
    ac_reg = 0;
    count_reg = 32;
end

always @(posedge clk) begin
    if (count_reg > 0) begin
        if (ac_reg[0] == 0 && ac_reg[1] == 0) begin
            // Shift right
            ac_reg = {ac_reg[30:0], m_reg[31]};
        end else if (ac_reg[0] == 1 && ac_reg[1] == 0) begin
            // Subtract
            ac_reg = ac_reg + (~m_reg + 1);
        end else if (ac_reg[0] == 0 && ac_reg[1] == 1) begin
            // Add
            ac_reg = ac_reg + m_reg;
        end
        count_reg = count_reg - 1;
    end
end

assign product = product_reg;

endmodule