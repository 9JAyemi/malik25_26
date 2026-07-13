module comparator_4bit_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [1:0] OUT
);
    // When A > B, OUT must be 01.
    check_gt_sets_code: assert property (
        @(posedge CLK) (A > B) |-> (OUT == 2'b01)
    );

    // When A < B, OUT must be 10.
    check_lt_sets_code: assert property (
        @(posedge CLK) (A < B) |-> (OUT == 2'b10)
    );

    // When A == B, OUT must be 11.
    check_eq_sets_code: assert property (
        @(posedge CLK) (A == B) |-> (OUT == 2'b11)
    );

    // OUT must never be 00.
    check_out_never_00: assert property (
        @(posedge CLK) (OUT != 2'b00)
    );

    // If OUT is 01, then A > B.
    check_code_implies_gt: assert property (
        @(posedge CLK) (OUT == 2'b01) |-> (A > B)
    );

    // If OUT is 10, then A < B.
    check_code_implies_lt: assert property (
        @(posedge CLK) (OUT == 2'b10) |-> (A < B)
    );

    // If OUT is 11, then A == B.
    check_code_implies_eq: assert property (
        @(posedge CLK) (OUT == 2'b11) |-> (A == B)
    );
endmodule