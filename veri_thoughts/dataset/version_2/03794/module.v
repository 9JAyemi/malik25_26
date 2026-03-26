
module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    output reg [7:0] final_output // 8-bit output from the functional module
);

wire [3:0] counter_out; // 4-bit output from the counter
wire [7:0] register_out; // 8-bit output from the register

// Instantiate the counter module
counter counter_inst (
    .clk(clk),
    .reset(reset),
    .out(counter_out)
);

// Instantiate the register module
reg8 reg8_inst (
    .clk(clk),
    .reset(reset),
    .out(register_out)
);

always @(counter_out, register_out) begin
   final_output = counter_out & register_out;
end

endmodule
module counter (
    input clk,
    input reset,
    output reg [3:0] out
);

always @(posedge clk) begin
    if (reset) begin
        out <= 4'b0000;
    end else begin
        out <= out + 1;
    end
end

endmodule
module reg8 (
    input clk,
    input reset,
    output reg [7:0] out
);

always @(posedge clk) begin
    if (reset) begin
        out <= 8'h34;
    end
end

endmodule