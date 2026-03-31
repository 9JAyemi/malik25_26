module tri_buf_sva (
    input logic A,
    input logic Z,
    input logic TE_B
);
    // No clock or reset in RTL; pure combinational. Sample on input edges.

    // Rising TE_B forces Z low immediately.
    check_z_low_on_teb_rise: assert property (
        @(posedge TE_B) (Z == 1'b0)
    );

    // Falling TE_B passes A to Z immediately.
    check_z_eq_a_on_teb_fall: assert property (
        @(negedge TE_B) (Z == A)
    );

    // When TE_B is low, Z follows A on A edges.
    check_pass_through_on_a_edges: assert property (
        @(posedge A or negedge A) (TE_B == 1'b0) |-> (Z == A)
    );

    // When TE_B is high, A edges do not affect Z (stays 0).
    check_a_edges_no_effect_when_teb_high: assert property (
        @(posedge A or negedge A) (TE_B == 1'b1) |-> (Z == 1'b0)
    );

endmodule