module johnson_counter_and (
    input clk,
    input reset,
    input [7:0] input_val,
    output [63:0] output_val
);

reg [63:0] counter;

always @(posedge clk) begin
    if (reset) begin
        counter <= 64'b0000_0000_0000_0000_0000_0000_0000_0000;
    end else begin
        counter <= {counter[62:0], counter[63] ^ counter[0]};
    end
end

assign output_val = counter & {64{input_val}};

endmodule