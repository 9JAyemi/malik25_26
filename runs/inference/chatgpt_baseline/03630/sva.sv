module multi_input_module_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1
);

    // A1, A2, and A3 high must force X high.
    check_a1_a2_a3_sets_x: assert property (
        @(posedge clk) (A1 & A2 & A3) |-> X
    );

    // A1, A2, and A4 high must force X high.
    check_a1_a2_a4_sets_x: assert property (
        @(posedge clk) (A1 & A2 & A4) |-> X
    );

    // A1, A3, and A4 high must force X high.
    check_a1_a3_a4_sets_x: assert property (
        @(posedge clk) (A1 & A3 & A4) |-> X
    );

    // A2, A3, and A4 high must force X high.
    check_a2_a3_a4_sets_x: assert property (
        @(posedge clk) (A2 & A3 & A4) |-> X
    );

    // A1, A2, and B1 high must force X high.
    check_a1_a2_b1_sets_x: assert property (
        @(posedge clk) (A1 & A2 & B1) |-> X
    );

    // A1, A3, and B1 high must force X high.
    check_a1_a3_b1_sets_x: assert property (
        @(posedge clk) (A1 & A3 & B1) |-> X
    );

    // A1, A4, and B1 high must force X high.
    check_a1_a4_b1_sets_x: assert property (
        @(posedge clk) (A1 & A4 & B1) |-> X
    );

    // A2, A3, and B1 high must force X high.
    check_a2_a3_b1_sets_x: assert property (
        @(posedge clk) (A2 & A3 & B1) |-> X
    );

    // A2, A4, and B1 high must force X high.
    check_a2_a4_b1_sets_x: assert property (
        @(posedge clk) (A2 & A4 & B1) |-> X
    );

    // A3, A4, and B1 high must force X high.
    check_a3_a4_b1_sets_x: assert property (
        @(posedge clk) (A3 & A4 & B1) |-> X
    );

    // X high must come from one of the RTL three-input product terms.
    check_x_requires_rtl_term: assert property (
        @(posedge clk) X |-> (
            (A1 & A2 & A3) |
            (A1 & A2 & A4) |
            (A1 & A3 & A4) |
            (A2 & A3 & A4) |
            (A1 & A2 & B1) |
            (A1 & A3 & B1) |
            (A1 & A4 & B1) |
            (A2 & A3 & B1) |
            (A2 & A4 & B1) |
            (A3 & A4 & B1)
        )
    );

endmodule