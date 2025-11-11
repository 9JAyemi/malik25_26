module rotator(
    input clk,
    input load,
    input [1:0] ena,
    input [99:0] data,
    output [99:0] q
);

reg [99:0] pipeline_reg [2:0];

always @(posedge clk) begin
    if (load) begin
        pipeline_reg[0] <= data;
        pipeline_reg[1] <= 100'b0;
        pipeline_reg[2] <= 100'b0;
    end else if (ena == 2'b01) begin
        pipeline_reg[0] <= {pipeline_reg[0][98:0], pipeline_reg[2][0]};
        pipeline_reg[1] <= pipeline_reg[0];
        pipeline_reg[2] <= {pipeline_reg[2][98:0], pipeline_reg[0][0]};
    end else if (ena == 2'b10) begin
        pipeline_reg[0] <= {pipeline_reg[1][98:1], pipeline_reg[0][0]};
        pipeline_reg[1] <= {pipeline_reg[2][98:1], pipeline_reg[1][0]};
        pipeline_reg[2] <= pipeline_reg[2];
    end else begin
        pipeline_reg[0] <= pipeline_reg[0];
        pipeline_reg[1] <= pipeline_reg[1];
        pipeline_reg[2] <= pipeline_reg[2];
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