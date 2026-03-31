module sky130_fd_sc_ls__o32ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);

    // Y matches the implemented NOR/OR/BUF function.
    check_output_function: assert property (
        @(posedge clk) Y == ((~(A1 | A2 | A3)) | (~(B1 | B2)))
    );

    // All A inputs high force Y low.
    check_a_inputs_all_high_force_low: assert property (
        @(posedge clk) (A1 && A2 && A3) |-> !Y
    );

    // All B inputs high force Y low.
    check_b_inputs_all_high_force_low: assert property (
        @(posedge clk) (B1 && B2) |-> !Y
    );

    // Any low A input and any low B input force Y high.
    check_any_a_low_and_any_b_low_force_high: assert property (
        @(posedge clk) ((!A1 || !A2 || !A3) && (!B1 || !B2)) |-> Y
    );

    // A low Y means at least one A input is high and at least one B input is high.
    check_low_output_implies_a_and_b_high: assert property (
        @(posedge clk) !Y |-> (A1 || A2 || A3) && (B1 || B2)
    );

    // A high Y means at least one A input is low and at least one B input is low.
    check_high_output_implies_a_and_b_low: assert property (
        @(posedge clk) Y |-> (!A1 || !A2 || !A3) && (!B1 || !B2)
    );

endmodule