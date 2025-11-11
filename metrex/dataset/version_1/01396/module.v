
module top_module (
    input signed [15:0] in1, // First 16-bit signed integer input
    input signed [15:0] in2, // Second 16-bit signed integer input
    output reg signed [15:0] sum_out, // 16-bit signed sum output
    input [15:0] absolute_in, // Input for absolute_value module
    output reg [15:0] max_out // 16-bit unsigned output from functional module
);

// Declare internal wires
wire [2:0] priority_input;

// Calculate sum of in1 and in2
always @* begin
    sum_out = in1 + in2;
end

// Assign priority encoder input
assign priority_input = {sum_out[15], absolute_in[15], sum_out[14:0] > absolute_in[14:0]};

// Use a case statement to determine max value
always @* begin
    case (priority_input)
        3'b000: max_out = 16'b0000000000000001;
        3'b001: max_out = 16'b0000000000000010;
        3'b010: max_out = 16'b0000000000000100;
        3'b011: max_out = 16'b0000000000001000;
        3'b100: max_out = 16'b0000000000010000;
        3'b101: max_out = 16'b0000000000100000;
        3'b110: max_out = 16'b0000000001000000;
        3'b111: max_out = 16'b0000000010000000;
        default: max_out = 16'b0000000000000000;
    endcase
end

endmodule

module absolute_value (
    input signed [15:0] in,
    output reg [15:0] out
);

always @* begin
    if (in < 0) begin
        out = ~in + 1;
    end
    else begin
        out = in;
    end
end

endmodule
