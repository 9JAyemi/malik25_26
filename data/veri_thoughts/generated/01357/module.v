module counter (
    input wire clk,
    input wire reset,
    input wire enable,
    output reg [15:0] count
);

    always @(posedge clk) begin
        if (reset) begin
            count <= 0;
        end else if (enable) begin
            count <= count + 1;
        end
    end

endmodule