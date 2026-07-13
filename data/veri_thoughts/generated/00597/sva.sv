module my_module_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    ///// Combinational function checks (sampled on posedge of A1) /////
    // Y must equal (A1 & A2 & A3) & (B1 | C1).
    check_y_matches_eqn: assert property (
        @(posedge A1) Y == ((A1 & A2 & A3) & (B1 | C1))
    );

    // If Y is HIGH, then A1,A2,A3 are HIGH and at least one of B1/C1 is HIGH.
    check_y_high_requires_all_as_and_one_of_bc: assert property (
        @(posedge A1) Y |-> (A1 & A2 & A3 & (B1 | C1))
    );

    // If A1 is LOW then Y must be LOW.
    check_y_zero_if_a1_zero: assert property (
        @(posedge A1) !A1 |-> !Y
    );

    // If A2 is LOW then Y must be LOW.
    check_y_zero_if_a2_zero: assert property (
        @(posedge A1) !A2 |-> !Y
    );

    // If A3 is LOW then Y must be LOW.
    check_y_zero_if_a3_zero: assert property (
        @(posedge A1) !A3 |-> !Y
    );

    // If both B1 and C1 are LOW then Y must be LOW.
    check_y_zero_if_b1_and_c1_zero: assert property (
        @(posedge A1) (!B1 && !C1) |-> !Y
    );

    // If A1,A2,A3 and B1 are HIGH then Y must be HIGH (independent of C1).
    check_y_one_if_all_as_and_b1_one: assert property (
        @(posedge A1) (A1 && A2 && A3 && B1) |-> Y
    );

    // If A1,A2,A3 and C1 are HIGH then Y must be HIGH (independent of B1).
    check_y_one_if_all_as_and_c1_one: assert property (
        @(posedge A1) (A1 && A2 && A3 && C1) |-> Y
    );

    // A rising edge on Y can only occur when A1,A2,A3 are HIGH and (B1|C1) is HIGH.
    check_y_rise_requires_inputs: assert property (
        @(posedge A1) $rose(Y) |-> (A1 && A2 && A3 && (B1 || C1))
    );

    // If inputs A1,A2,A3,B1,C1 are unchanged between samples, Y must be unchanged.
    check_y_stable_if_inputs_stable: assert property (
        @(posedge A1) ({A1,A2,A3,B1,C1} == $past({A1,A2,A3,B1,C1})) |-> (Y == $past(Y))
    );
endmodule