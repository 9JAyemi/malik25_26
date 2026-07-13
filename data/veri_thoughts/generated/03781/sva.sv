module custom_module_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

    // Y must match the implemented O221A boolean function.
    check_o221a_function: assert property (
        @(posedge clk)
        Y === ((A1 & A2) | (B1 & B2 & C1))
    );

    // A1 and A2 high must force Y high.
    check_a_term_drives_y: assert property (
        @(posedge clk)
        ((A1 & A2) === 1'b1) |-> (Y === 1'b1)
    );

    // B1, B2, and C1 high must force Y high.
    check_b_term_drives_y: assert property (
        @(posedge clk)
        ((B1 & B2 & C1) === 1'b1) |-> (Y === 1'b1)
    );

    // If neither product term is true, Y must be low.
    check_no_term_means_y_low: assert property (
        @(posedge clk)
        (((A1 & A2) | (B1 & B2 & C1)) === 1'b0) |-> (Y === 1'b0)
    );

    // A high Y must be caused by one of the implemented product terms.
    check_y_high_has_valid_cause: assert property (
        @(posedge clk)
        (Y === 1'b1) |-> (((A1 & A2) | (B1 & B2 & C1)) === 1'b1)
    );

endmodule