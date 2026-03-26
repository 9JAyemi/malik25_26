module my_module_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // X matches the implemented OR-of-AND function.
    check_output_function: assert property (
        @(posedge clk) X == ((A1 & A2) | B1)
    );

    // B1 drives X high through the OR gate.
    check_b1_forces_high: assert property (
        @(posedge clk) B1 |-> X
    );

    // The A1/A2 AND term drives X high when B1 is low.
    check_and_term_drives_high: assert property (
        @(posedge clk) (!B1 && A1 && A2) |-> X
    );

    // A low A1 forces X low when B1 is low.
    check_a1_low_forces_low_without_b1: assert property (
        @(posedge clk) (!B1 && !A1) |-> !X
    );

    // A low A2 forces X low when B1 is low.
    check_a2_low_forces_low_without_b1: assert property (
        @(posedge clk) (!B1 && !A2) |-> !X
    );

    // A high X must come from B1 or the A1/A2 AND term.
    check_high_output_has_valid_cause: assert property (
        @(posedge clk) X |-> (B1 || (A1 && A2))
    );

    // A low X means B1 is low and the AND term is not asserted.
    check_low_output_has_valid_cause: assert property (
        @(posedge clk) !X |-> (!B1 && (!A1 || !A2))
    );

endmodule