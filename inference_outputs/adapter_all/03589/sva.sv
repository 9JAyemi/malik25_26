module addsub_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic SUB,
    input logic [3:0] OUT,
    input logic COUT
);
    // COUT equals MSB of (A + (SUB ? ~B : B)).
    check_cout_matches_sum_msb: assert property (
        @(posedge SUB or negedge SUB or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3])
        COUT == ((A + (SUB ? ~B : B))[3])
    );

    // OUT equals (SUB ? (~B + 1) : (A + B)) masked to 4 bits.
    check_out_matches_sum_masked: assert property (
        @(posedge SUB or negedge SUB or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3])
        OUT == ((SUB ? (~B + 4'b0001) : (A + B)) & 4'hF)
    );

    // When SUB=0, OUT equals A+B (masked to 4 bits).
    check_add_path_out: assert property (
        @(posedge SUB or negedge SUB or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3])
        !SUB |-> (OUT == ((A + B) & 4'hF))
    );

    // When SUB=1, OUT equals (~B + 1) (masked to 4 bits).
    check_sub_path_out: assert property (
        @(posedge SUB or negedge SUB or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3])
        SUB |-> (OUT == ((~B + 4'b0001) & 4'hF))
    );

    // When SUB=0, COUT equals MSB of (A + B).
    check_cout_add_path: assert property (
        @(posedge SUB or negedge SUB or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3])
        !SUB |-> (COUT == ((A + B)[3]))
    );

    // When SUB=1, COUT equals MSB of (A + (~B + 1)).
    check_cout_sub_path: assert property (
        @(posedge SUB or negedge SUB or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3])
        SUB |-> (COUT == ((A + (~B + 4'b0001))[3]))
    );

    // When SUB=0, OUT equals (A + B) masked to 4 bits.
    check_out_add_path: assert property (
        @(posedge SUB or negedge SUB or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3])
        !SUB |-> (OUT == ((A + B) & 4'hF))
    );

    // When SUB=1, OUT equals (~B + 1) masked to 4 bits.
    check_out_sub_path: assert property (
        @(posedge SUB or negedge SUB or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3])
        SUB |-> (OUT == ((~B + 4'b0001) & 4'hF))
    );

    // When SUB=0, OUT equals (A + B) masked to 4 bits.
    check_out_add_path_masked: assert property (
        @(posedge SUB or negedge SUB or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3])
        !SUB |-> (OUT == ((A + B) & 4'hF))
    );

    // When SUB=1, OUT equals (~B + 1) masked to 4 bits.
    check_out_sub_path_masked: assert property (
        @(posedge SUB or negedge SUB or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3])
        SUB |-> (OUT == ((~B + 4'b0001) & 4'hF))
    );

    // When SUB=0, OUT equals (A + B) masked to 4 bits.
    check_out_add_path_masked: assert property (
        @(posedge SUB or negedge SUB or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge A[2] or negedge A[2] or posedge A[3] or negedge A[3] or posedge B[0] or negedge B[0] or posedge B[1] or negedge B[1] or posedge B[2] or negedge B[2] or posedge B[3] or negedge B[3])
        !SUB |-> (OUT == ((A + B) & 4'hF))
    );

    // When SUB=1, OUT equals (~B + 1) masked to 4 bits.
    check_out_sub_path_masked: assert property (
        @(posedge SUB or negedge SUB or posedge A[0] or negedge A[0] or posedge A[1] or negedge A[1] or posedge