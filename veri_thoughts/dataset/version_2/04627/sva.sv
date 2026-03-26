module sky130_fd_sc_hd__a31oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

    // Y matches the implemented AOI31 function.
    check_y_matches_aoi31: assert property (
        @(posedge clk) Y === ~(B1 | (A1 & A2 & A3))
    );

    // B1 high forces the NOR output low.
    check_b1_high_forces_y_low: assert property (
        @(posedge clk) B1 |-> (Y === 1'b0)
    );

    // With B1 low, all three A inputs high force Y low.
    check_all_a_high_with_b1_low_forces_y_low: assert property (
        @(posedge clk) (!B1 && A1 && A2 && A3) |-> (Y === 1'b0)
    );

    // With B1 low, any low A input forces Y high.
    check_not_all_a_high_with_b1_low_forces_y_high: assert property (
        @(posedge clk) (!B1 && !(A1 && A2 && A3)) |-> (Y === 1'b1)
    );

    // Y can be high only when B1 is low and the AND term is low.
    check_y_high_only_when_nor_inputs_low: assert property (
        @(posedge clk) (Y === 1'b1) |-> (!B1 && !(A1 && A2 && A3))
    );

    // Y can be low only when B1 is high or the AND term is high.
    check_y_low_only_when_nor_input_high: assert property (
        @(posedge clk) (Y === 1'b0) |-> (B1 || (A1 && A2 && A3))
    );

endmodule