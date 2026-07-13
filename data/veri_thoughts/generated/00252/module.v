module pipelined_xor_gate (
    input clk, // Clock signal
    input a,
    input b,
    output reg out // Output should be a reg if driven by an always block
);

// Pipeline registers
reg a_reg, b_reg;

// Clocked always block for pipeline
always @(posedge clk) begin
    a_reg <= a;
    b_reg <= b;
    out <= a_reg ^ b_reg; // Perform XOR in the sequential logic
end

endmodule
