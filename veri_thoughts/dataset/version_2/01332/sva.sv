module add_sub_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic SUB,
    input logic [3:0] OUT
);

    // When SUB is 0, OUT must equal A + B (4-bit).
    check_add_path: assert property (
        @(posedge SUB or negedge SUB
          or posedge A[0] or negedge A[0]
          or posedge A[1] or negedge A[1]
          or posedge A[2] or negedge A[2]
          or posedge A[3] or negedge A[3]
          or posedge B[0] or negedge B[0]
          or posedge B[1] or negedge B[1]
          or posedge B[2] or negedge B[2]
          or posedge B[3] or negedge B[3]
          or posedge OUT[0] or negedge OUT[0]
          or posedge OUT[1] or negedge OUT[1]
          or posedge OUT[2] or negedge OUT[2]
          or posedge OUT[3] or negedge OUT[3]
        ) (!SUB) |-> (OUT == (A + B))
    );

    // When SUB is 1, OUT must equal B - A (4-bit).
    check_sub_path: assert property (
        @(posedge SUB or negedge SUB
          or posedge A[0] or negedge A[0]
          or posedge A[1] or negedge A[1]
          or posedge A[2] or negedge A[2]
          or posedge A[3] or negedge A[3]
          or posedge B[0] or negedge B[0]
          or posedge B[1] or negedge B[1]
          or posedge B[2] or negedge B[2]
          or posedge B[3] or negedge B[3]
          or posedge OUT[0] or negedge OUT[0]
          or posedge OUT[1] or negedge OUT[1]
          or posedge OUT[2] or negedge OUT[2]
          or posedge OUT[3] or negedge OUT[3]
        ) (SUB) |-> (OUT == (B - A))
    );

endmodule