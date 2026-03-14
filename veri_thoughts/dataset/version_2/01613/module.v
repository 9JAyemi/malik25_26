
module counter (
    input Clk,
    input Reset,
    input Enable,
    output [3:0] Q
);

reg [3:0] Q_reg;
reg [3:0] Q_next;

always @(posedge Clk) begin
    if (Reset) begin
        Q_reg <= 4'b0000;
    end else if (Enable) begin
        Q_reg <= Q_next;
    end
end

always @(*) begin
    if (Enable)
        Q_next = Q_reg + 1;
    else
        Q_next = Q_reg;
end

assign Q = Q_reg;

endmodule
