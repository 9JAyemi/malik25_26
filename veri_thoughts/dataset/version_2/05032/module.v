module dff_16 (
    input clk,
    input reset,
    input [15:0] d,
    output reg [15:0] q
    );

    always @(posedge clk) begin
        if (reset) begin
            q <= 16'b0;
        end else begin
            q <= d;
        end
    end

endmodule