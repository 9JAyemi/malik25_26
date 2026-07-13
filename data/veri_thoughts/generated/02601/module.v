
module binary_counter (
    input clk,
    input reset,
    input enable,
    output [3:0] Q
);

reg [3:0] Q_reg;
reg [3:0] Q_next;

always @(posedge clk) begin
    if (reset) begin
        Q_reg <= 4'b0;
    end
    else if (enable) begin
        Q_reg <= Q_next;
    end
end

always @* begin
    if (Q_reg == 4'b1111) begin
        Q_next = 4'b0000;
    end
    else begin
        Q_next = Q_reg + 1;
    end
end

assign Q = Q_reg;

endmodule
