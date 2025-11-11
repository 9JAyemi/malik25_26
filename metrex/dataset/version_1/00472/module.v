module counter_4bit (
    input clk,
    input rst,
    output reg [3:0] Q
);

    always @(posedge clk or posedge rst) begin
        if (rst) begin
            Q <= 4'b0000;
        end else begin
            Q <= Q + 1;
        end
    end

endmodule