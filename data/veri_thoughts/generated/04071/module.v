module up_down_counter (
    input clk,
    input up_down,
    input reset,
    output reg [2:0] Q
);

    always @(posedge clk) begin
        if (reset) begin
            Q <= 3'b0;
        end else if (up_down) begin
            Q <= Q + 1;
        end else begin
            Q <= Q - 1;
        end
    end

endmodule