module binary_counter (
    input clk,
    input reset,
    output reg [3:0] Q
);

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            Q <= 4'b0000;
        end else begin
            Q <= Q + 1;
        end
    end

endmodule