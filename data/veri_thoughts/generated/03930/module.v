module full_adder (
    input A,
    input B,
    input Cin,
    output Sum,
    output Cout
);
    assign {Cout, Sum} = A + B + Cin;
endmodule

module ripple_adder (
    input [3:0] A,
    input [3:0] B,
    output [3:0] C
);

    wire [3:0] sum;
    wire [3:0] carry;

    full_adder fa0(A[0], B[0], 1'b0, sum[0], carry[0]);
    full_adder fa1(A[1], B[1], carry[0], sum[1], carry[1]);
    full_adder fa2(A[2], B[2], carry[1], sum[2], carry[2]);
    full_adder fa3(A[3], B[3], carry[2], sum[3], carry[3]);

    assign C = sum;

endmodule

module mux (
    input [3:0] in0,
    input [3:0] in1,
    input [3:0] in2,
    input [3:0] in3,
    input [1:0] sel,
    output reg [3:0] out
);

    always @(*) begin
        case (sel)
            2'b00: out = in0;
            2'b01: out = in1;
            2'b10: out = in2;
            2'b11: out = in3;
        endcase
    end

endmodule

module and_gate (
    input [3:0] in1,
    input [3:0] in2,
    output [3:0] out
);

    assign out = in1 & in2;

endmodule

module top_module (
    input [3:0] A,
    input [3:0] B,
    input [3:0] in0,
    input [3:0] in1,
    input [3:0] in2,
    input [3:0] in3,
    input [1:0] sel,
    output [3:0] out
);

    wire [3:0] adder_out;
    wire [3:0] mux_out;

    ripple_adder adder(A, B, adder_out);
    mux mux_inst(in0, in1, in2, in3, sel, mux_out);
    and_gate and_gate_inst(adder_out, mux_out, out);

endmodule