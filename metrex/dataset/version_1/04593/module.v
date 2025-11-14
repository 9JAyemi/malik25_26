
module OR_gate_pipeline(
    input a,
    input b,
    input clk,  // Added clock input
    output reg out
);

reg p1_out;

always @ (a, b) begin
    p1_out <= a | b;
end

always @ (posedge clk) begin
    out <= p1_out;
end

endmodule

module top_module(
    input a,
    input b,
    input clk,  // Added clock input
    output out
);

OR_gate_pipeline or_gate_pipeline(
    .a(a),
    .b(b),
    .clk(clk),  // Connect the clock input
    .out(out)  // Directly connect the output of OR_gate_pipeline to the output of top_module
);

endmodule
