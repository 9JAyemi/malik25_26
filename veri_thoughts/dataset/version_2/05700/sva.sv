module sky130_fd_sc_ls__fahcin_sva (
    input logic clk,
    input logic COUT,
    input logic SUM,
    input logic A,
    input logic B,
    input logic CIN
);

    // External sampling clock; DUT has no clock or reset.

    // SUM matches A xor B xor inverted CIN.
    check_sum_function: assert property (
        @(posedge clk) SUM == (A ^ B ^ (~CIN))
    );

    // COUT matches the OR of the three carry product terms.
    check_cout_function: assert property (
        @(posedge clk) COUT == ((A & B) | (A & (~CIN)) | (B & (~CIN)))
    );

    // With CIN high, the inverted carry-in term is zero.
    check_cin_high_mode: assert property (
        @(posedge clk) CIN |-> ((SUM == (A ^ B)) && (COUT == (A & B)))
    );

    // With CIN low, the inverted carry-in term is one.
    check_cin_low_mode: assert property (
        @(posedge clk) !CIN |-> ((SUM == (~(A ^ B))) && (COUT == (A | B)))
    );

    // When both data inputs are low, carry out stays low.
    check_inputs_00: assert property (
        @(posedge clk) (!A && !B) |-> ((SUM == (~CIN)) && (COUT == 1'b0))
    );

    // When both data inputs are high, carry out stays high.
    check_inputs_11: assert property (
        @(posedge clk) (A && B) |-> ((SUM == (~CIN)) && (COUT == 1'b1))
    );

    // When only A is high, outputs depend only on CIN inversion.
    check_inputs_10: assert property (
        @(posedge clk) (A && !B) |-> ((SUM == CIN) && (COUT == (~CIN)))
    );

    // When only B is high, outputs depend only on CIN inversion.
    check_inputs_01: assert property (
        @(posedge clk) (!A && B) |-> ((SUM == CIN) && (COUT == (~CIN)))
    );

    // Equal A and B produce SUM equal to inverted CIN and COUT equal to A.
    check_equal_inputs_relation: assert property (
        @(posedge clk) !(A ^ B) |-> ((SUM == (~CIN)) && (COUT == A))
    );

    // Unequal A and B produce SUM equal to CIN and COUT equal to inverted CIN.
    check_unequal_inputs_relation: assert property (
        @(posedge clk) (A ^ B) |-> ((SUM == CIN) && (COUT == (~CIN)))
    );

endmodule