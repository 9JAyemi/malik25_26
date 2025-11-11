
module counter (
    input clk,
    input rst,
    input en,
    input up,
    output reg [3:0] count
);

reg [3:0] count_reg1, count_reg2;

always @(posedge clk) begin
    if (rst) begin
        count_reg1 <= 4'b0;
        count_reg2 <= 4'b0;
    end
    else begin
        if (en) begin
            if (up) begin
                count_reg1 <= count_reg2 + 4'b1;
            end
            else begin
                count_reg1 <= count_reg2 - 4'b1;
            end
        end
        count_reg2 <= count_reg1;
    end
end

always @(posedge clk) begin
    if (rst) begin
        count <= 4'b0;
    end
    else begin
        count <= count_reg2;
    end
end

endmodule
