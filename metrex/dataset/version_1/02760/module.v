
module rotator(
    input clk,
    input load,
    input [1:0] ena,
    input [99:0] data,
    output [99:0] q
);

reg [99:0] stage1_data;
reg [99:0] stage2_data;
reg [99:0] stage3_data;

always @(posedge clk) begin
    if(load) begin
        stage1_data <= data;
        stage2_data <= stage1_data;
        stage3_data <= stage2_data;
    end else if(ena == 2'b01) begin // left rotation
        stage1_data <= {stage1_data[98:0], stage1_data[99]};
        stage2_data <= {stage2_data[97:0], stage2_data[99:98]};
        stage3_data <= {stage3_data[96:0], stage3_data[99:97]};
    end else if(ena == 2'b10) begin // right rotation
        stage1_data <= {stage1_data[1:99], stage1_data[0]};
        stage2_data <= {stage2_data[2:99], stage2_data[1:0]};
        stage3_data <= {stage3_data[3:99], stage3_data[2:0]};
    end
end

assign q = ena == 2'b00 ? data : ena == 2'b01 ? stage1_data : ena == 2'b10 ? stage2_data : stage3_data;

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