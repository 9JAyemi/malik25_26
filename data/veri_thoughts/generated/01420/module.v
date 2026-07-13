
module twos_complement (
    input clk,
    input reset,
    input [3:0] in,
    output reg [3:0] out
);

    // Combinational logic for 2's complement
    wire [3:0] temp_out = ~in + 4'b1;

    // Synchronous reset
    always @(posedge clk) begin
        if (reset) begin
            out <= 4'b0;
        end else begin
            out <= temp_out;
        end
    end

endmodule