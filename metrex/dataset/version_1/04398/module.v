
module reverse_bit_order_pipeline(
    input clk,
    input reset,
    input [7:0] in,
    output [7:0] out
);

// Register to hold the input data
reg [7:0] in_reg;

// Register to hold the reversed output data
reg [7:0] out_reg;

// Pipeline register to hold the reversed data
reg [7:0] out_pipeline_reg;

always @(posedge clk) begin
    // Reset logic
    if (reset) begin
        in_reg <= 8'b0;
        out_reg <= 8'b0;
        out_pipeline_reg <= 8'b0;
    end else begin
        // Store the input data in the register
        in_reg <= in;

        // Reverse the input data and store it in the output register
        out_reg <= {in_reg[7], in_reg[6], in_reg[5], in_reg[4],
                   in_reg[3], in_reg[2], in_reg[1], in_reg[0]};

        // Store the reversed data in the pipeline register
        out_pipeline_reg <= out_reg;
    end
end

// Assign the output to the pipeline register
assign out = out_pipeline_reg;

endmodule

module top_module(
    input clk,
    input reset,
    input [7:0] in,
    output [7:0] out
);

reverse_bit_order_pipeline reverse_inst(
    .clk(clk),
    .reset(reset),
    .in(in),
    .out(out)
);

endmodule
