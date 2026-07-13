module adder_subtractor_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic SUB,
    input logic [3:0] SUM
);

// SUM equals A + B when SUB is 0.
    check_add_mode: assert property (
        @(posedge CLK) !SUB |-> (SUM == (A + B))
    );

// SUM equals A + (B's 2's complement) when SUB is 1.
    check_sub_mode: assert property (
        @(posedge CLK) SUB |-> (SUM == (A + ((~B) + 4'b0001)))
    );

// In add mode, SUM equals A + B (4-bit wraparound).
    check_add_result: assert property (
        @(posedge CLK) !SUB |-> (SUM == (A + B))
    );

// In sub mode, SUM equals A + (B's 2's complement) (4-bit wraparound).
    check_sub_result: assert property (
        @(posedge CLK) SUB |-> (SUM == (A + ((~B) + 4'b0001)))
    );

// In sub mode, SUM equals A - B (4-bit wraparound).
    check_sub_result_alt: assert property (
        @(posedge CLK) SUB |-> (SUM == (A - B))
    );

// In add mode, SUM equals A + B (4-bit wraparound).
    check_add_result_alt: assert property (
        @(posedge CLK) !SUB |-> (SUM == (A + B))
    );

// In sub mode, SUM equals A + (B's 2's complement) (4-bit wraparound).
    check_sub_result_alt2: assert property (
        @(posedge CLK) SUB |-> (SUM == (A + ((~B) + 4'b0001)))
    );

// In sub mode, SUM equals A - B (4-bit wraparound).
    check_sub_result_alt3: assert property (
        @(posedge CLK) SUB |-> (SUM == (A - B))
    );

endmodule
