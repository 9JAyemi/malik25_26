
module and_gate_pipeline(
    input a, 
    input b,
    input clk,  // Added clock input
    output reg out
);

reg pipe1_out;
reg pipe2_out;

always @ (posedge clk) begin
    pipe1_out <= a & b;
end

always @ (posedge clk) begin
    pipe2_out <= pipe1_out;
end

always @ (posedge clk) begin
    out <= pipe2_out;
end

endmodule
