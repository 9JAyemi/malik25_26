module xnor4to1_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y
);
    // Y must equal the 4-input XNOR of A,B,C,D.
    check_y_matches_xnor: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
        Y == ~(A ^ B ^ C ^ D)
    );

    // If A==B and C==D, Y must be 1.
    check_pairs_equal_y1: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
        ((A == B) && (C == D)) |-> (Y == 1'b1)
    );

    // If exactly one of (A==B) or (C==D) holds, Y must be 0.
    check_one_pair_equal_y0: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
        (((A == B) ^ (C == D)) == 1'b1) |-> (Y == 1'b0)
    );

    // If A!=B and C!=D, Y must be 1.
    check_no_pairs_equal_y1: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
        ((A != B) && (C != D)) |-> (Y == 1'b1)
    );

endmodule