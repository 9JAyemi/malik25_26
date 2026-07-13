module my_module_assertions (
    input  logic       clk,
    input  logic [1:0] A1,
    input  logic [1:0] A2,
    input  logic [1:0] B1,
    input  logic [1:0] B2,
    input  logic [1:0] C1,
    input  logic [1:0] VPWR,
    input  logic [1:0] VGND,
    input  logic [1:0] VPB,
    input  logic [1:0] VNB,
    input  logic       X
);

    // RTL has no clock or reset; clk is an external sampling clock.
    // DUT logic is combinational, and X is driven only by A1/A2/B1/B2.

    // X must equal the implemented compare function.
    check_x_matches_compare_function: assert property (
        @(posedge clk) X === (((A1 == B1) && (A2 == B2)) ? 1'b1 : 1'b0)
    );

    // X must be high when both compared pairs match.
    check_x_high_when_both_pairs_match: assert property (
        @(posedge clk) ((A1 == B1) && (A2 == B2)) |-> (X === 1'b1)
    );

    // X must be low when only A2/B2 mismatch.
    check_x_low_when_only_second_pair_mismatches: assert property (
        @(posedge clk) ((A1 == B1) && (A2 != B2)) |-> (X === 1'b0)
    );

    // X must be low when only A1/B1 mismatch.
    check_x_low_when_only_first_pair_mismatches: assert property (
        @(posedge clk) ((A1 != B1) && (A2 == B2)) |-> (X === 1'b0)
    );

    // X must be low when both compared pairs mismatch.
    check_x_low_when_both_pairs_mismatch: assert property (
        @(posedge clk) ((A1 != B1) && (A2 != B2)) |-> (X === 1'b0)
    );

endmodule