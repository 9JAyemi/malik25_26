module counter_4bit (
    input clk,
    input reset,
    input enable,
    output reg [3:0] Q
);

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            Q <= 4'b0000;
        end else if (enable) begin
            Q <= Q + 1;
        end
    end

endmodule