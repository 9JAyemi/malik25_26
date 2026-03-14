
module top_module (
    input clk,
    input reset,
    input [99:0] in,
    output out_and,
    output out_or,
    output out_xor,
    output [3:0] Q,
    output reg [3:0] out_sum
);

// AND-OR-XOR circuit
wire and_out;
wire or_out;
wire xor_out;

and_gate and_inst (
    .a(in[0]),
    .b(in[1]),
    .y(and_out)
);

or_gate or_inst (
    .a(in[0]),
    .b(in[1]),
    .y(or_out)
);

xor_gate xor_inst (
    .a(in[0]),
    .b(in[1]),
    .y(xor_out)
);

assign out_and = and_out;
assign out_or = or_out;
assign out_xor = xor_out;

// Johnson counter
reg [3:0] johnson_counter = 4'b0000;

always @(posedge clk) begin
    if (reset) begin
        johnson_counter <= 4'b0000;
    end else begin
        case (johnson_counter)
            4'b0000: johnson_counter <= 4'b0001;
            4'b0001: johnson_counter <= 4'b0011;
            4'b0011: johnson_counter <= 4'b0111;
            4'b0111: johnson_counter <= 4'b1111;
            4'b1111: johnson_counter <= 4'b1110;
            4'b1110: johnson_counter <= 4'b1100;
            4'b1100: johnson_counter <= 4'b1000;
            4'b1000: johnson_counter <= 4'b0000;
        endcase
    end
end

assign Q = johnson_counter;

// Additional functional module
always @(*) begin
    case (johnson_counter)
        4'b0001: out_sum = xor_out + 4'b0001;
        4'b0011: out_sum = xor_out + 4'b0011;
        4'b0111: out_sum = xor_out + 4'b0111;
        4'b1111: out_sum = xor_out + 4'b1111;
        4'b1110: out_sum = xor_out + 4'b1110;
        4'b1100: out_sum = xor_out + 4'b1100;
        4'b1000: out_sum = xor_out + 4'b1000;
        default: out_sum = 4'b0000;
    endcase
end

endmodule
module and_gate (
    input a,
    input b,
    output y
);

assign y = a & b;

endmodule
module or_gate (
    input a,
    input b,
    output y
);

assign y = a | b;

endmodule
module xor_gate (
    input a,
    input b,
    output y
);

assign y = a ^ b;

endmodule