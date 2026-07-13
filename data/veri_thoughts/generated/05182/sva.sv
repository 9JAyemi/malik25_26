module four_input_or_gate_assertions (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C,
    input logic [3:0] D,
    input logic       VPWR,
    input logic       VGND,
    input logic       VPB,
    input logic       VNB,
    input logic       X
);

    // X is the reduction OR of all bits from A, B, C, and D.
    check_output_matches_reduction_or: assert property (
        @(posedge clk) X == (|{A, B, C, D})
    );

    // All-zero data inputs force X low.
    check_zero_inputs_produce_zero: assert property (
        @(posedge clk) ({A, B, C, D} == 16'h0000) |-> (X == 1'b0)
    );

    // X low implies all data input bits are low.
    check_output_low_implies_all_inputs_low: assert property (
        @(posedge clk) (X == 1'b0) |-> ({A, B, C, D} == 16'h0000)
    );

    // X high implies at least one data input bit is high.
    check_output_high_implies_some_input_high: assert property (
        @(posedge clk) (X == 1'b1) |-> (|{A, B, C, D})
    );

    // Any asserted bit in A forces X high.
    check_a_nonzero_sets_output: assert property (
        @(posedge clk) (|A) |-> (X == 1'b1)
    );

    // Any asserted bit in B forces X high.
    check_b_nonzero_sets_output: assert property (
        @(posedge clk) (|B) |-> (X == 1'b1)
    );

    // Any asserted bit in C forces X high.
    check_c_nonzero_sets_output: assert property (
        @(posedge clk) (|C) |-> (X == 1'b1)
    );

    // Any asserted bit in D forces X high.
    check_d_nonzero_sets_output: assert property (
        @(posedge clk) (|D) |-> (X == 1'b1)
    );

endmodule