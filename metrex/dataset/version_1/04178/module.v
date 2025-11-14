module counter (
    input clk,
    input Up,
    input Down,
    input Load,
    input Reset,
    output reg [2:0] Q
);

    always @(posedge clk) begin
        if (Reset) begin
            Q <= 3'b000;
        end else if (Load) begin
            Q <= 3'b111;
        end else if (Up) begin
            Q <= Q + 1;
        end else if (Down) begin
            Q <= Q - 1;
        end
    end

endmodule