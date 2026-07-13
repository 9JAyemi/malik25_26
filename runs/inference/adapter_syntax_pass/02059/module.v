
module twos_complement (
    input [3:0] A, // 4-bit input to be twos complemented
    output [3:0] OUT // 4-bit twos complement output
);

assign OUT = ~A + 1;

endmodule

module mux_2to1 (
    input [3:0] A, // 4-bit input 1
    input [3:0] B, // 4-bit input 2
    input sel, // Select input
    output [3:0] OUT // 4-bit output
);

assign OUT = sel ? A : B;

endmodule

module top_module (
    input [3:0] A, // 4-bit input for twos complement
    input [3:0] B, // 4-bit input for mux
    input sel, // Select input for mux
    output [3:0] OUT // 4-bit output from mux
);

wire [3:0] wire_twos_comp; // Renamed wire to avoid duplicate declaration error

twos_complement twos_comp(
    .A(A),
    .OUT(wire_twos_comp)
);

mux_2to1 mux(
    .A(wire_twos_comp),
    .B(B),
    .sel(sel),
    .OUT(OUT)
);

endmodule
