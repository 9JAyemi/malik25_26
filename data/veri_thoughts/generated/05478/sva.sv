module adder_subtractor_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic CIN,
    input logic SUB,
    input logic [7:0] SUM,
    input logic OVF
);

    // In add mode, SUM is the low 8 bits of A plus B.
    check_add_mode_sum: assert property (
        @(posedge clk)
        (!SUB) |-> (SUM == (A + B))
    );

    // In subtract mode, SUM is the low 8 bits of A plus two's-complement B.
    check_sub_mode_sum: assert property (
        @(posedge clk)
        (SUB) |-> (SUM == (A + (~B + 8'h01)))
    );

    // OVF is never asserted when CIN is low.
    check_no_ovf_without_cin: assert property (
        @(posedge clk)
        (!CIN) |-> (OVF == 1'b0)
    );

    // With CIN high in add mode, outputs match the 9-bit sum of A and B.
    check_add_with_cin: assert property (
        @(posedge clk)
        (!SUB && CIN) |-> ({OVF, SUM} == ({1'b0, A} + {1'b0, B}))
    );

    // With CIN high in subtract mode, outputs match the 9-bit sum of A and two's-complement B.
    check_sub_with_cin: assert property (
        @(posedge clk)
        (SUB && CIN) |-> ({OVF, SUM} == ({1'b0, A} + {1'b0, (~B + 8'h01)}))
    );

endmodule