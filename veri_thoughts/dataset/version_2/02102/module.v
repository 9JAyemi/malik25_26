module top_module (
    input clk,
    input reset, // Synchronous active-high reset
    input [7:0] in_data, // Input data to the system
    output reg out_signal // Output signal of the system
);

reg [7:0] shift_reg; // Byte-wide shift register
reg parity; // Parity generator output
reg d_ff; // D flip-flop module output
reg xor_output; // XOR module output

// Byte-wide shift register
always @(posedge clk) begin
    if (reset) begin
        shift_reg <= 8'b0;
    end else begin
        shift_reg <= {shift_reg[6:0], parity};
    end
end

// Parity generator
always @(*) begin
    parity = ^in_data;
end

// D flip-flop module
always @(posedge clk) begin
    if (reset) begin
        d_ff <= 1'b0;
    end else begin
        d_ff <= in_data[0];
    end
end

// XOR module
always @(*) begin
    xor_output = parity ^ d_ff;
end

// Output signal
always @(posedge clk) begin
    if (reset) begin
        out_signal <= 1'b0;
    end else begin
        out_signal <= shift_reg[7];
    end
end

endmodule