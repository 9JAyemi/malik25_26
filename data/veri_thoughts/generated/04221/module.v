module up_down_counter (
    input clk,
    input up_down,
    input load,
    input reset,
    input [3:0] D,
    output reg [3:0] Q
);

    always @(posedge clk) begin
        if (reset) begin
            Q <= 4'b0;
        end
        else if (load) begin
            Q <= D;
        end
        else if (up_down) begin
            Q <= Q + 1;
        end
        else begin
            Q <= Q - 1;
        end
    end

endmodule