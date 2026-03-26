
module pipelined_vector (
    input wire [2:0] vec,
    input wire clk,  // Added clock input
    output wire [2:0] outv,
    output wire o2,
    output wire o1,
    output wire o0
);

reg [2:0] stage1_out;
reg [2:0] stage2_out;
reg [2:0] stage3_out;

assign o2 = vec[2];
assign o1 = vec[1];
assign o0 = vec[0];

always @ (posedge clk) begin  // Corrected always block
    stage1_out <= vec;
end

always @ (posedge clk) begin  // Corrected always block
    stage2_out <= stage1_out;
end

always @ (posedge clk) begin  // Corrected always block
    stage3_out <= stage2_out;
end

assign outv = stage3_out;

endmodule
