module counter (
    input clk,
    input rst,
    input up_down,
    output [3:0] count
);

    reg [3:0] count_reg;

    always @(posedge clk) begin
        if (rst) begin
            count_reg <= 4'b0000;
        end else begin
            if (up_down == 1) begin
                if (count_reg == 4'b0000) begin
                    count_reg <= 4'b1111;
                end else begin
                    count_reg <= count_reg - 1;
                end
            end else begin
                if (count_reg == 4'b1111) begin
                    count_reg <= 4'b0000;
                end else begin
                    count_reg <= count_reg + 1;
                end
            end
        end
    end

    assign count = count_reg;

endmodule