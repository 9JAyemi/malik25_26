module up_down_counter_4bit (
    input clk,
    input Up,
    input Down,
    output reg [3:0] Q
);

    always @(posedge clk) begin
        if (Up) begin
            if (Q == 4'b1111) begin
                Q <= 4'b0000;
            end else begin
                Q <= Q + 1;
            end
        end else if (Down) begin
            if (Q == 4'b0000) begin
                Q <= 4'b1111;
            end else begin
                Q <= Q - 1;
            end
        end
    end

endmodule