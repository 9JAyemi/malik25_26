module up_down_counter (
    input CLK, UP_DOWN, RESET,
    output reg [3:0] Q
);

reg [3:0] Q_reg;
reg [3:0] Q_next;

always @(posedge CLK) begin
    if(RESET) begin
        Q_reg <= 4'b0;
    end
    else begin
        Q_reg <= Q_next;
    end
end

always @* begin
    if(UP_DOWN) begin
        Q_next = Q_reg + 1;
    end
    else begin
        Q_next = Q_reg - 1;
    end
end

always @* begin
    Q = Q_reg;
end

endmodule