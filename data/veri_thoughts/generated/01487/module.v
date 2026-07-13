module counter #(
    parameter WIDTH = 8,
    parameter MODULUS = 256
)(
    input clk,
    input ce,
    input clr,
    output reg [WIDTH-1:0] out
);

    always @(posedge clk) begin
        if (clr) begin
            out <= 0;
        end else if (ce) begin
            out <= (out == MODULUS-1) ? 0 : out + 1;
        end
    end

endmodule