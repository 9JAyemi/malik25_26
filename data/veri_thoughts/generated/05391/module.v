module counter_4bit (
    input clk,
    input reset,
    output reg [3:0] Q
);

    always @(posedge clk or negedge reset) begin
        if (reset == 0) begin
            Q <= 4'b0000;
        end
        else begin
            Q <= Q + 1;
        end
    end

endmodule