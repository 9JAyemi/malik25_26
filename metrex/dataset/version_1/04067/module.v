module concat_module (
    input clk,
    input [89:0] in,
    output reg [44:0] line0,
    output reg [44:0] line1,
    output reg [89:0] out
);

    always @(posedge clk) begin
        line0 <= in[44:0];
        line1 <= in[89:45];
        out <= {line0, line1};
    end

endmodule