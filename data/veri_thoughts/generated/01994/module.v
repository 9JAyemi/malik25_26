
module adder_8bit (
    input         clk,
    input  [7:0] input_a,
    input  [7:0] input_b,
    output reg [7:0] output_c
);

    always @(posedge clk) begin
        output_c <= input_a + input_b;
    end

endmodule