// All listed RTL primitives are combinational and have no RTL reset; clk is an external sampling clock for SVA.

module MISTRAL_ALUT6_sva #(
    parameter [63:0] LUT = 64'h0000_0000_0000_0000
) (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic E,
    input logic F,
    input logic Q
);
    // Q equals the LUT bit selected by F:A.
    check_alut6_selected_lut_bit: assert property (
        @(posedge clk) Q == LUT[{F, E, D, C, B, A}]
    );
endmodule

module MISTRAL_ALUT5_sva #(
    parameter [31:0] LUT = 32'h0000_0000
) (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic E,
    input logic Q
);
    // Q equals the LUT bit selected by E:A.
    check_alut5_selected_lut_bit: assert property (
        @(posedge clk) Q == LUT[{E, D, C, B, A}]
    );
endmodule

module MISTRAL_ALUT4_sva #(
    parameter [15:0] LUT = 16'h0000
) (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Q
);
    // Q equals the LUT bit selected by D:A.
    check_alut4_selected_lut_bit: assert property (
        @(posedge clk) Q == LUT[{D, C, B, A}]
    );
endmodule

module MISTRAL_ALUT3_sva #(
    parameter [7:0] LUT = 8'h00
) (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic Q
);
    // Q equals the LUT bit selected by C:A.
    check_alut3_selected_lut_bit: assert property (
        @(posedge clk) Q == LUT[{C, B, A}]
    );
endmodule

module MISTRAL_ALUT2_sva #(
    parameter [3:0] LUT = 4'h0
) (
    input logic clk,
    input logic A,
    input logic B,
    input logic Q
);
    // Q equals the LUT bit selected by B:A.
    check_alut2_selected_lut_bit: assert property (
        @(posedge clk) Q == LUT[{B, A}]
    );
endmodule

module MISTRAL_NOT_sva (
    input logic clk,
    input logic A,
    input logic Q
);
    // Q is the bitwise inversion of A.
    check_not_inverts_input: assert property (
        @(posedge clk) Q == ~A
    );
endmodule

module MISTRAL_ALUT_ARITH_sva #(
    parameter [15:0] LUT0 = 16'h0000,
    parameter [15:0] LUT1 = 16'h0000
) (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D0,
    input logic D1,
    input logic CI,
    input logic SO,
    input logic CO
);
    // SO is the sum bit of q0 + !q1 + CI.
    check_alut_arith_sum_bit: assert property (
        @(posedge clk)
        SO == (LUT0[{D0, C, B, A}] ^ (!LUT1[{D1, C, B, A}]) ^ CI)
    );

    // CO is the carry bit of q0 + !q1 + CI.
    check_alut_arith_carry_bit: assert property (
        @(posedge clk)
        CO == ((LUT0[{D0, C, B, A}] & (!LUT1[{D1, C, B, A}])) |
               (LUT0[{D0, C, B, A}] & CI) |
               ((!LUT1[{D1, C, B, A}]) & CI))
    );
endmodule