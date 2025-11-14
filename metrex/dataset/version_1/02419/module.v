module wire_recorder(
    input wire clk,
    input wire reset,
    input wire [156:0] input_vector,
    input wire [129:0] output_vector,
    output reg [156:0] input_vector_reg,
    output reg [129:0] output_vector_reg,
    output reg clk_start
);


always @(posedge clk) begin
    if(reset) begin
        input_vector_reg <= 0;
        output_vector_reg <= 0;
        clk_start <= 1'b0;
    end else begin
        input_vector_reg <= input_vector;
        output_vector_reg <= output_vector;
        clk_start <= (output_vector_reg[0] == 1'b1) ? 1'b1 : clk_start; 
    end
end

endmodule
