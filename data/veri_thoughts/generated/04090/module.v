
module top_module (
    input CLK,
    input CLR,
    input LD,
    input [3:0] DATA,
    output [3:0] Y
);
// Temp Reg
wire [3:0] counter_output;
wire [3:0] bitwise_and_output;

// Sub Modules
counter counter_inst (
    .CLK(CLK),
    .CLR(CLR),
    .LD(LD),
    .DATA(DATA),
    // Output Ports
    .Q(counter_output)
);

bitwise_and bitwise_and_inst (
    .A(counter_output),
    .B(DATA),
    // Output Ports
    .Y(bitwise_and_output)
);

functional_module functional_module_inst (
    .counter_output(counter_output),
    .bitwise_and_output(bitwise_and_output),
    // Output Ports
    .final_output(Y)
);

endmodule

module counter (
    input CLK,
    input CLR,
    input LD,
    input [3:0] DATA,
    // Output Ports
    output reg [3:0] Q
);

always @(posedge CLK or negedge CLR) begin
    if (CLR == 0) begin
        Q <= 0;
    end else if (LD == 1) begin
        Q <= DATA;
    end else begin
        Q <= Q + 1;
        if (Q == 16) begin
            Q <= 0;
        end
    end
end

endmodule

module bitwise_and (
    input [3:0] A,
    input [3:0] B,
    // Output Ports
    output reg [3:0] Y
);

always @(A or B) begin
  Y = A & B;
end

endmodule

module functional_module (
    input [3:0] counter_output,
    input [3:0] bitwise_and_output,
    // Output Ports
    output reg [3:0] final_output
);

always @(counter_output or bitwise_and_output) begin
  final_output = bitwise_and_output & counter_output;
end

endmodule
