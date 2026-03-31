module my_buffer_sva (
    input logic A,
    input logic Z,
    input logic TE_B,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

    ///// Functional equivalence /////
    // Z must equal TE_B & A when sampled on A rising.
    check_func_equiv_on_A: assert property (
        @(posedge A) Z == (TE_B & A)
    );

    // Z must equal TE_B & A when sampled on TE_B rising.
    check_func_equiv_on_TEB: assert property (
        @(posedge TE_B) Z == (TE_B & A)
    );

    ///// Enable low forces zero /////
    // If TE_B is LOW, Z must be 0 (sampled on A rising).
    check_zero_when_teb_low_on_A: assert property (
        @(posedge A) (TE_B == 1'b0) |-> (Z == 1'b0)
    );

    ///// Enable high passes A /////
    // If TE_B is HIGH, Z equals A (sampled on A rising).
    check_passthrough_when_teb_high_on_A: assert property (
        @(posedge A) (TE_B == 1'b1) |-> (Z == A)
    );

    // On TE_B rising (now HIGH), Z must equal A.
    check_passthrough_on_teb_rise: assert property (
        @(posedge TE_B) Z == A
    );

    ///// Output implications /////
    // If Z is HIGH, both TE_B and A must be HIGH (sampled on A rising).
    check_z_high_implies_inputs_high_on_A: assert property (
        @(posedge A) (Z == 1'b1) |-> (TE_B == 1'b1 && A == 1'b1)
    );

endmodule