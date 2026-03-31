module adder_8bit_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic Cin,
    input logic [7:0] Sum,
    input logic Cout
);

    // Combined output equals the 9-bit addition result.
    check_full_add_result: assert property (
        @(posedge clk) {Cout, Sum} == ({1'b0, A} + {1'b0, B} + {8'b0, Cin})
    );

    // Sum matches the low 8 bits of the addition.
    check_sum_low_byte: assert property (
        @(posedge clk) Sum == (({1'b0, A} + {1'b0, B} + {8'b0, Cin})[7:0])
    );

    // Cout matches the carry-out bit of the addition.
    check_cout_high_bit: assert property (
        @(posedge clk) Cout == (({1'b0, A} + {1'b0, B} + {8'b0, Cin})[8])
    );

    // Zero on B with no carry-in leaves A unchanged.
    check_b_zero_identity: assert property (
        @(posedge clk) (B == 8'h00 && Cin == 1'b0) |-> (Sum == A && Cout == 1'b0)
    );

    // Zero on A with no carry-in leaves B unchanged.
    check_a_zero_identity: assert property (
        @(posedge clk) (A == 8'h00 && Cin == 1'b0) |-> (Sum == B && Cout == 1'b0)
    );

    // With both operands zero, Sum reflects Cin and Cout stays low.
    check_cin_only_case: assert property (
        @(posedge clk) (A == 8'h00 && B == 8'h00) |-> (Sum == {7'b0, Cin} && Cout == 1'b0)
    );

    // Carry-out is low when the 9-bit result is below 256.
    check_no_carry_range: assert property (
        @(posedge clk) (({1'b0, A} + {1'b0, B} + {8'b0, Cin}) < 9'h100) |-> (Cout == 1'b0)
    );

    // Carry-out is high when the 9-bit result reaches 256 or more.
    check_carry_range: assert property (
        @(posedge clk) (({1'b0, A} + {1'b0, B} + {8'b0, Cin}) >= 9'h100) |-> (Cout == 1'b1)
    );

endmodule