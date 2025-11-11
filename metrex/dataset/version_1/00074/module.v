module byte_reverse (
    input [31:0] in,
    output [31:0] out
);
    assign out = {in[7:0], in[15:8], in[23:16], in[31:24]};
endmodule

module decade_counter (
    input clk,
    input reset,
    input slowena,
    output reg [3:0] count
);
    always @(posedge clk or negedge reset) begin
        if (!reset) begin
            count <= 4'b0;
        end else if (!slowena) begin
            count <= count;
        end else begin
            count <= count + 1;
        end
    end
endmodule

module adder (
    input [31:0] in1,
    input [3:0] in2,
    output [31:0] out
);
    assign out = in1 + in2;
endmodule

module top_module (
    input clk,
    input reset,
    input slowena,
    input [31:0] in,
    output [31:0] out
);
    wire [31:0] byte_reversed;
    wire [3:0] counter;
    byte_reverse byte_reverse_inst (
        .in(in),
        .out(byte_reversed)
    );
    decade_counter decade_counter_inst (
        .clk(clk),
        .reset(reset),
        .slowena(slowena),
        .count(counter)
    );
    adder adder_inst (
        .in1(byte_reversed),
        .in2(counter),
        .out(out)
    );
endmodule