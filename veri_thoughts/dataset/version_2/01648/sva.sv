module Half_Subtractor_sva (
    input logic A,
    input logic B,
    input logic D,
    input logic Bout
);
    // D equals A xor B.
    hs_check_diff_eq: assert property (
        @(posedge A or negedge A or posedge B or negedge B) D == (A ^ B)
    );
    // Bout is asserted iff A < B.
    hs_check_bout_eq: assert property (
        @(posedge A or negedge A or posedge B or negedge B) Bout == (A < B)
    );
    // When inputs are equal, D is 0.
    hs_check_equal_inputs_diff0: assert property (
        @(posedge A or negedge A or posedge B or negedge B) (A == B) |-> (D == 1'b0)
    );
    // When inputs are equal, Bout is 0.
    hs_check_equal_inputs_bout0: assert property (
        @(posedge A or negedge A or posedge B or negedge B) (A == B) |-> (Bout == 1'b0)
    );
    // When A=0 and B=1, Bout is 1.
    hs_check_borrow_case_01: assert property (
        @(posedge A or negedge A or posedge B or negedge B) ((A == 1'b0) && (B == 1'b1)) |-> (Bout == 1'b1)
    );
    // When A=1 and B=0, Bout is 0.
    hs_check_borrow_case_10: assert property (
        @(posedge A or negedge A or posedge B or negedge B) ((A == 1'b1) && (B == 1'b0)) |-> (Bout == 1'b0)
    );
endmodule

module Full_Subtractor_sva (
    input logic A,
    input logic B,
    input logic Bin,
    input logic D,
    input logic Bout
);
    // D equals A xor B xor Bin.
    fs_check_diff_eq: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge Bin or negedge Bin) D == (A ^ B ^ Bin)
    );
    // Bout equals (A < B) | (Bin & (A <= B)).
    fs_check_bout_eq: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge Bin or negedge Bin) Bout == ((A < B) | (Bin & (A <= B)))
    );
    // With Bin=0, D reduces to A xor B.
    fs_check_bin0_diff: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge Bin or negedge Bin) (Bin == 1'b0) |-> (D == (A ^ B))
    );
    // With Bin=0, Bout reduces to (A < B).
    fs_check_bin0_bout: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge Bin or negedge Bin) (Bin == 1'b0) |-> (Bout == (A < B))
    );
    // With Bin=1, D equals ~(A xor B).
    fs_check_bin1_diff_not: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge Bin or negedge Bin) (Bin == 1'b1) |-> (D == ~(A ^ B))
    );
    // When A==B, D equals Bin.
    fs_check_equal_inputs_diff_bin: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge Bin or negedge Bin) (A == B) |-> (D == Bin)
    );
    // When A==B, Bout equals Bin.
    fs_check_equal_inputs_bout_bin: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge Bin or negedge Bin) (A == B) |-> (Bout == Bin)
    );
    // When A=0 and B=1, Bout is 1 regardless of Bin.
    fs_check_borrow_case_01: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge Bin or negedge Bin) ((A == 1'b0) && (B == 1'b1)) |-> (Bout == 1'b1)
    );
    // When A=1 and B=0, Bout is 0 regardless of Bin.
    fs_check_borrow_case_10: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge Bin or negedge Bin) ((A == 1'b1) && (B == 1'b0)) |-> (Bout == 1'b0)
    );
endmodule