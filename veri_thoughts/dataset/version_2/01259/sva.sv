module four_to_one_sva (
    input logic CLK,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2,
    input logic Y
);
    // Y implements the exact combinational equation from RTL.
    func_equivalence: assert property (
        @(posedge CLK)
        Y == ( !(A1_N && A2_N && B1 && !B2)
             && !(A1_N && !A2_N && !B1 && B2)
             && !(!A1_N && A2_N && !B1 && B2)
             && !(!A1_N && !A2_N && B1 && B2) )
    );

    // Minterm A1_N&A2_N&B1&~B2 forces Y LOW.
    minterm1_forces_low: assert property (
        @(posedge CLK) (A1_N && A2_N && B1 && !B2) |-> (Y == 1'b0)
    );

    // Minterm A1_N&~A2_N&~B1&B2 forces Y LOW.
    minterm2_forces_low: assert property (
        @(posedge CLK) (A1_N && !A2_N && !B1 && B2) |-> (Y == 1'b0)
    );

    // Minterm ~A1_N&A2_N&~B1&B2 forces Y LOW.
    minterm3_forces_low: assert property (
        @(posedge CLK) (!A1_N && A2_N && !B1 && B2) |-> (Y == 1'b0)
    );

    // Minterm ~A1_N&~A2_N&B1&B2 forces Y LOW.
    minterm4_forces_low: assert property (
        @(posedge CLK) (!A1_N && !A2_N && B1 && B2) |-> (Y == 1'b0)
    );

    // If none of the minterms hold, Y must be HIGH.
    none_minterm_forces_high: assert property (
        @(posedge CLK)
        !( (A1_N && A2_N && B1 && !B2)
         || (A1_N && !A2_N && !B1 && B2)
         || (!A1_N && A2_N && !B1 && B2)
         || (!A1_N && !A2_N && B1 && B2) ) |-> (Y == 1'b1)
    );

    // Y LOW implies at least one minterm is true.
    y_low_implies_some_minterm: assert property (
        @(posedge CLK)
        (Y == 1'b0) |-> ( (A1_N && A2_N && B1 && !B2)
                       || (A1_N && !A2_N && !B1 && B2)
                       || (!A1_N && A2_N && !B1 && B2)
                       || (!A1_N && !A2_N && B1 && B2) )
    );

    // With stable inputs, Y must remain stable (purely combinational).
    stable_output_when_inputs_stable: assert property (
        @(posedge CLK)
        ($stable(A1_N) && $stable(A2_N) && $stable(B1) && $stable(B2)) |-> $stable(Y)
    );

    // When B1=0 and B2=0, Y must be HIGH.
    b00_forces_high: assert property (
        @(posedge CLK) (!B1 && !B2) |-> (Y == 1'b1)
    );

    // When B1=1 and B2=0 and not(A1_N&A2_N), Y must be HIGH.
    b10_nonbothA_high_forces_high: assert property (
        @(posedge CLK) (B1 && !B2 && !(A1_N && A2_N)) |-> (Y == 1'b1)
    );

    // When B1=0 and B2=1 and A1_N^A2_N, Y must be LOW.
    b01_xor_forces_low: assert property (
        @(posedge CLK) (!B1 && B2 && (A1_N ^ A2_N)) |-> (Y == 1'b0)
    );

    // When B1=0 and B2=1 and A1_N==A2_N, Y must be HIGH.
    b01_xnor_forces_high: assert property (
        @(posedge CLK) (!B1 && B2 && !(A1_N ^ A2_N)) |-> (Y == 1'b1)
    );

    // When B1=1 and B2=1 and any A is HIGH, Y must be HIGH.
    b11_anyA_high_forces_high: assert property (
        @(posedge CLK) (B1 && B2 && (A1_N || A2_N)) |-> (Y == 1'b1)
    );
endmodule