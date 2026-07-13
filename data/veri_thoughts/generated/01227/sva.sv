module sky130_fd_sc_ls__a222oi_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic C2
);
    // Y equals ~((A1&A2)|(B1&B2)|(C1&C2)) sampled on A1 rising.
    func_eq_on_A1: assert property (
        @(posedge A1) Y == ( !(A1 & A2) && !(B1 & B2) && !(C1 & C2) )
    );
    // Y equals ~((A1&A2)|(B1&B2)|(C1&C2)) sampled on A2 rising.
    func_eq_on_A2: assert property (
        @(posedge A2) Y == ( !(A1 & A2) && !(B1 & B2) && !(C1 & C2) )
    );
    // Y equals ~((A1&A2)|(B1&B2)|(C1&C2)) sampled on B1 rising.
    func_eq_on_B1: assert property (
        @(posedge B1) Y == ( !(A1 & A2) && !(B1 & B2) && !(C1 & C2) )
    );
    // Y equals ~((A1&A2)|(B1&B2)|(C1&C2)) sampled on B2 rising.
    func_eq_on_B2: assert property (
        @(posedge B2) Y == ( !(A1 & A2) && !(B1 & B2) && !(C1 & C2) )
    );
    // Y equals ~((A1&A2)|(B1&B2)|(C1&C2)) sampled on C1 rising.
    func_eq_on_C1: assert property (
        @(posedge C1) Y == ( !(A1 & A2) && !(B1 & B2) && !(C1 & C2) )
    );
    // Y equals ~((A1&A2)|(B1&B2)|(C1&C2)) sampled on C2 rising.
    func_eq_on_C2: assert property (
        @(posedge C2) Y == ( !(A1 & A2) && !(B1 & B2) && !(C1 & C2) )
    );
    // Y equals ~((A1&A2)|(B1&B2)|(C1&C2)) sampled on Y rising.
    func_eq_on_Y: assert property (
        @(posedge Y) Y == ( !(A1 & A2) && !(B1 & B2) && !(C1 & C2) )
    );
    // If A1&A2 are both 1, Y must be 0 (sampled on A1 rising).
    pairA_forces_low_on_A1: assert property (
        @(posedge A1) (A1 && A2) |-> (Y == 1'b0)
    );
    // If B1&B2 are both 1, Y must be 0 (sampled on B1 rising).
    pairB_forces_low_on_B1: assert property (
        @(posedge B1) (B1 && B2) |-> (Y == 1'b0)
    );
    // If C1&C2 are both 1, Y must be 0 (sampled on C1 rising).
    pairC_forces_low_on_C1: assert property (
        @(posedge C1) (C1 && C2) |-> (Y == 1'b0)
    );
endmodule