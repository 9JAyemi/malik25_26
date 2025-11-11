
module rotator(
    input clk,
    input load,
    input [1:0] ena,
    input [99:0] data,
    output [99:0] q
);

reg [99:0] pipeline_reg [2:0];
reg [99:0] shifted_out;
reg [99:0] shifted_in;

always @(posedge clk) begin
    if (load) begin
        pipeline_reg[0] <= data;
        pipeline_reg[1] <= pipeline_reg[0];
        pipeline_reg[2] <= pipeline_reg[1];
    end else begin
        pipeline_reg[0] <= shifted_in;
        pipeline_reg[1] <= pipeline_reg[0];
        pipeline_reg[2] <= pipeline_reg[1];
    end
    
    if (ena == 2'b01) begin
        shifted_out <= pipeline_reg[2][0];
        shifted_in <= {shifted_out, pipeline_reg[2][99:1]};
    end else if (ena == 2'b10) begin
        shifted_out <= pipeline_reg[2][99];
        shifted_in <= {pipeline_reg[2][98:0], shifted_out};
    end else begin
        shifted_in <= pipeline_reg[2];
    end
end

assign q = pipeline_reg[0];

endmodule

module top_module(
    input clk,
    input load,
    input [1:0] ena,
    input [99:0] data,
    output [99:0] q
);

rotator rotator_inst(
    .clk(clk),
    .load(load),
    .ena(ena),
    .data(data),
    .q(q)
);

endmodule
