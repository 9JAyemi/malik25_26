module compare_module_sva (
    input logic [1:0] A,
    input logic       B,
    input logic       Z
);
    // No clock or reset in DUT; combinational logic only. Sample on posedges of inputs.

    // Z equals (A >= B) when sampled on B's rising edge.
    check_func_eq_on_B: assert property (
        @(posedge B) Z == (A >= B)
    );

    // Z equals (A >= B) when sampled on A[0]'s rising edge.
    check_func_eq_on_A0: assert property (
        @(posedge A[0]) Z == (A >= B)
    );

    // Z equals (A >= B) when sampled on A[1]'s rising edge.
    check_func_eq_on_A1: assert property (
        @(posedge A[1]) Z == (A >= B)
    );

    // If B is 0, Z must be 1 (A is unsigned and >= 0).
    check_b0_implies_z1: assert property (
        @(posedge A[0]) (B == 1'b0) |-> (Z == 1'b1)
    );

    // If B is 1 and A is 0, Z must be 0 (0 >= 1 is false).
    check_b1_a0_implies_z0: assert property (
        @(posedge A[1]) (B == 1'b1 && A == 2'b00) |-> (Z == 1'b0)
    );

    // If B is 1 and A != 0, Z must be 1 (A in {1,2,3} >= 1).
    check_b1_a_nonzero_implies_z1: assert property (
        @(posedge A[0]) (B == 1'b1 && A != 2'b00) |-> (Z == 1'b1)
    );
endmodule