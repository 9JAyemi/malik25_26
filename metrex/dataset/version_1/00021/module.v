module binary_counter (
    input clk,              // Clock input
    input reset,            // Synchronous active-high reset
    output reg [3:0] count  // 4-bit binary counter output
);

always @(posedge clk) begin
    if (reset) begin
        count <= 4'b0000;
    end else begin
        count <= count + 1;
    end
end

endmodule

module register (
    input clk,              // Clock input
    input reset,            // Synchronous active-high reset
    input [7:0] d,          // 8-bit input
    output reg [7:0] q      // 8-bit output
);

always @(posedge clk) begin
    if (reset) begin
        q <= 8'h34;
    end else begin
        q <= d;
    end
end

endmodule

module control_logic (
    input select,           // Select input to choose between register and counter
    input [7:0] reg_out,    // Output from the register module
    input [3:0] counter_out,// Output from the binary_counter module
    output [7:0] out        // Output of the selected module
);

assign out = select ? reg_out : counter_out;

endmodule

module top_module (
    input clk,              // Clock input
    input reset,            // Synchronous active-high reset
    input [7:0] d,          // 8-bit input for the register
    input select,           // Select input to choose between register and counter
    output [7:0] q          // 8-bit output from the active module
);

wire [3:0] counter_out;
wire [7:0] reg_out;

binary_counter counter_inst (
    .clk(clk),
    .reset(reset),
    .count(counter_out)
);

register reg_inst (
    .clk(clk),
    .reset(reset),
    .d(d),
    .q(reg_out)
);

control_logic control_inst (
    .select(select),
    .reg_out(reg_out),
    .counter_out(counter_out),
    .out(q)
);

endmodule