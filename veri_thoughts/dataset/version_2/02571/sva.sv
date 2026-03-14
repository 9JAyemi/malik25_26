module sky130_fd_sc_hdll__a22o_sva (
    input logic CLK,        // external assertion clock
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic and0_out,   // internal: B1 & B2
    input logic and1_out,   // internal: A1 & A2
    input logic or0_out_X   // internal: and1_out | and0_out
);
    // X equals (A1 & A2) | (B1 & B2).
    check_x_function: assert property (
        @(posedge CLK) X == ((A1 & A2) | (B1 & B2))
    );

    // and0_out equals (B1 & B2).
    check_and0_out_function: assert property (
        @(posedge CLK) and0_out == (B1 & B2)
    );

    // and1_out equals (A1 & A2).
    check_and1_out_function: assert property (
        @(posedge CLK) and1_out == (A1 & A2)
    );

    // or0_out_X equals and1_out | and0_out.
    check_or0_out_function: assert property (
        @(posedge CLK) or0_out_X == (and1_out | and0_out)
    );

    // X equals or0_out_X (buffer connectivity).
    check_buf_connectivity: assert property (
        @(posedge CLK) X == or0_out_X
    );

    // If A1&A2 are HIGH, X must be HIGH.
    check_x_high_if_a_pair_high: assert property (
        @(posedge CLK) (A1 && A2) |-> (X == 1'b1)
    );

    // If B1&B2 are HIGH, X must be HIGH.
    check_x_high_if_b_pair_high: assert property (
        @(posedge CLK) (B1 && B2) |-> (X == 1'b1)
    );

    // If neither pair is HIGH, X must be LOW.
    check_x_zero_if_no_pairs_high: assert property (
        @(posedge CLK) (!(A1 && A2) && !(B1 && B2)) |-> (X == 1'b0)
    );

    // X HIGH requires at least one pair to be HIGH.
    check_x_high_requires_some_pair: assert property (
        @(posedge CLK) (X == 1'b1) |-> ((A1 && A2) || (B1 && B2))
    );

    // X LOW requires that no pair is HIGH.
    check_x_low_requires_no_pair: assert property (
        @(posedge CLK) (X == 1'b0) |-> (!((A1 && A2) || (B1 && B2)))
    );
endmodule