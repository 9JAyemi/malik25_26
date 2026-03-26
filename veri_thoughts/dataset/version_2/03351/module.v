
module top_module (
    input wire clk,
    input wire reset,
    input wire [15:0] in,
    output reg [7:0] final_output
);

reg [7:0] upper_byte;
reg [7:0] lower_byte;
wire [7:0] xor_output;

// Instantiate module 1
module1 module1_inst (
    .clk(clk),
    .reset(reset),
    .in(in),
    .upper_byte(upper_byte),
    .lower_byte(lower_byte)
);

// Instantiate module 2
module2 module2_inst (
    .in1(upper_byte),
    .in2(lower_byte),
    .out(xor_output)
);

// XOR the lower byte of the input with the output of module 2
always @ (posedge clk) begin
    if (reset) final_output <= 8'b0;
    else final_output <= xor_output ^ lower_byte;
end

endmodule
module module1 (
    input wire clk,
    input wire reset,
    input wire [15:0] in,
    output reg [7:0] upper_byte,
    output reg [7:0] lower_byte
);

always @ (posedge clk) begin
    if (reset) begin
        upper_byte <= 8'b0;
        lower_byte <= 8'b0;
    end else begin
        upper_byte <= in[15:8];
        lower_byte <= in[7:0];
    end
end

endmodule
module module2 (
    input wire [7:0] in1,
    input wire [7:0] in2,
    output reg [7:0] out
);

always @ (*) begin
    out <= in1 ^ in2;
end

endmodule