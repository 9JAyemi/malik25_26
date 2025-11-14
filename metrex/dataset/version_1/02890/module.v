
module top_module (
    input clk,
    input reset,   // Synchronous active-high reset
    input [31:0] in,
    output [15:0] q,
    output [3:0] ena
);

wire [31:0] transition_detected;
wire [15:0] bcd_counter;

// Detect 1 to 0 transitions
transition_detector td (
    .clk(clk),
    .reset(reset),
    .in(in),
    .out(transition_detected)
);

// BCD counter
bcd_counter bc (
    .clk(clk),
    .reset(reset),
    .ena(ena[3]),
    .out(bcd_counter)
);

// Max value selector
max_value_selector mvs (
    .in1(transition_detected),
    .in2(bcd_counter),
    .out(q)
);

assign ena = 4'b0; // Fix the undriven wires

endmodule
module transition_detector (
    input clk,
    input reset,
    input [31:0] in,
    output [31:0] out
);

reg [31:0] in_prev;

always @(posedge clk or posedge reset) begin
    if (reset) begin
        in_prev <= 32'b0;
    end else begin
        in_prev <= in;
    end
end

assign out = in_prev & ~in;

endmodule
module bcd_counter (
    input clk,
    input reset,
    input ena,
    output [15:0] out
);

reg [15:0] count;

always @(posedge clk or posedge reset) begin
    if (reset) begin
        count <= 16'b0;
    end else if (ena) begin
        count <= count + 1'b1;
        if (count == 16'h9999) begin
            count <= 16'b0;
        end
    end
end

assign out = count;

endmodule
module max_value_selector (
    input [31:0] in1,
    input [15:0] in2,
    output [15:0] out
);

assign out = (in1 > in2) ? in1[15:0] : in2;

endmodule