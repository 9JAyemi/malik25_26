module add_sub_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic SUB,
    input logic [3:0] OUT
);

// When SUB is 0, OUT equals A + B.
    check_add_mode_result: assert property (
        @(posedge clk) !SUB |-> (OUT == (A + B))
    );

// When SUB is 1, OUT equals B - A.
    check_sub_mode_result: assert property (
        @(posedge clk) SUB |-> (OUT == (B - A))
    );

// In add mode, equal inputs produce zero.
    check_add_equal_inputs_zero: assert property (
        @(posedge clk) (!SUB && (A == B)) |-> (OUT == 4'h0)
    );

// In sub mode, equal inputs produce zero.
    check_sub_equal_inputs_zero: assert property (
        @(posedge clk) (SUB && (A == B)) |-> (OUT == 4'h0)
    );

// In add mode, 0 on B passes A through.
    check_add_b_zero_passthrough: assert property (
        @(posedge clk) (!SUB && (B == 4'h0)) |-> (OUT == A)
    );

// In sub mode, 0 on A passes B through.
    check_sub_a_zero_passthrough: assert property (
        @(posedge clk) (SUB && (A == 4'h0)) |-> (OUT == B)
    );

// In add mode, 0xF on B is a 4-bit increment.
    check_add_b_15_increment: assert property (
        @(posedge clk) (!SUB && (B == 4'hF)) |-> (OUT == (A + 4'h1))
    );

// In sub mode, 0xF on A is a 4-bit decrement.
    check_sub_a_15_decrement: assert property (
        @(posedge clk) (SUB && (A == 4'hF)) |-> (OUT == (B - 4'h1))
    );

endmodule
