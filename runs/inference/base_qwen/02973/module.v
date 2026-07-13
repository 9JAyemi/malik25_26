module up_down_counter (
    input clk,
    input reset,
    input load,
    input up_down,
    output reg [3:0] count
);

reg [3:0] count_reg;
reg [3:0] count_next;

always @(posedge clk) begin
    if (reset) begin
        count_reg <= 4'b0000;
    end else begin
        count_reg <= count_next;
    end
end

always @* begin
    if (load) begin
        count_next = count;
    end else if (up_down) begin
        count_next = count_reg + 4'b0001;
    end else begin
        count_next = count_reg - 4'b0001;
    end
end

always @* begin
    count = count_reg;
end

endmodule