module demux4x1_sva (
    input  logic CLK,
    input  logic Q0,
    input  logic Q1,
    input  logic Q2,
    input  logic Q3,
    input  logic D,
    input  logic S1,
    input  logic S0
);
    // When S1S0==00, Q0==D and others are 0.
    sel00_routes_d_to_q0: assert property (
        @(posedge CLK) (!S1 && !S0) |-> (Q0 == D && (Q1 == 1'b0) && (Q2 == 1'b0) && (Q3 == 1'b0))
    );

    // When S1S0==01, Q1==D and others are 0.
    sel01_routes_d_to_q1: assert property (
        @(posedge CLK) (!S1 &&  S0) |-> (Q1 == D && (Q0 == 1'b0) && (Q2 == 1'b0) && (Q3 == 1'b0))
    );

    // When S1S0==10, Q2==D and others are 0.
    sel10_routes_d_to_q2: assert property (
        @(posedge CLK) ( S1 && !S0) |-> (Q2 == D && (Q0 == 1'b0) && (Q1 == 1'b0) && (Q3 == 1'b0))
    );

    // When S1S0==11, Q3==D and others are 0.
    sel11_routes_d_to_q3: assert property (
        @(posedge CLK) ( S1 &&  S0) |-> (Q3 == D && (Q0 == 1'b0) && (Q1 == 1'b0) && (Q2 == 1'b0))
    );

    // If Q0 is HIGH, then D=1 and S1S0==00.
    q0_high_implies_sel00_and_d: assert property (
        @(posedge CLK) (Q0 == 1'b1) |-> (D == 1'b1 && !S1 && !S0)
    );

    // If Q1 is HIGH, then D=1 and S1S0==01.
    q1_high_implies_sel01_and_d: assert property (
        @(posedge CLK) (Q1 == 1'b1) |-> (D == 1'b1 && !S1 &&  S0)
    );

    // If Q2 is HIGH, then D=1 and S1S0==10.
    q2_high_implies_sel10_and_d: assert property (
        @(posedge CLK) (Q2 == 1'b1) |-> (D == 1'b1 &&  S1 && !S0)
    );

    // If Q3 is HIGH, then D=1 and S1S0==11.
    q3_high_implies_sel11_and_d: assert property (
        @(posedge CLK) (Q3 == 1'b1) |-> (D == 1'b1 &&  S1 &&  S0)
    );

    // Outputs are at most one-hot at all times.
    outputs_onehot0: assert property (
        @(posedge CLK) $onehot0({Q3, Q2, Q1, Q0})
    );

    // OR of all outputs equals D.
    or_of_outputs_matches_d: assert property (
        @(posedge CLK) ((Q0 | Q1 | Q2 | Q3) == D)
    );
endmodule