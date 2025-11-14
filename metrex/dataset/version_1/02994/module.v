module counter_4bit (
    input clk,
    input rst,
    input en,
    output reg [3:0] count
);

    always @(posedge clk or negedge rst) begin
        if (~rst) begin
            count <= 4'b0;
        end else if (en) begin
            count <= count + 1;
        end
    end

endmodule