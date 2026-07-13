module shift_reg (
    input d,
    input clk,
    input en,
    output reg [7:0] q
);

reg [7:0] shift_reg;

always @(posedge clk) begin
    if (en) begin
        shift_reg <= {shift_reg[6:0], d};
    end
end

always @(*) begin
    q = shift_reg;
end

endmodule