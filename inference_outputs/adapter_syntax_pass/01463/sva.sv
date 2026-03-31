module arithmetic_module_sva (
    input logic clk,
    input logic Boo_ba1,
    input logic Boo_ba2,
    input logic b,
    input logic Boo_ba3,
    input logic c,
    input logic [3:0] f4_dotnamed
);

    // f4 is the sum of the three submodules' outputs.
    check_f4_sum: assert property (
        @(posedge clk)
        f4_dotnamed == ((Boo_ba1 << 1) + (Boo_ba2 + b) + (Boo_ba3 - c))
    );

    // The SubA contribution is always zero or one.
    check_suba_contribution_range: assert property (
        @(posedge clk)
        ((Boo_ba1 << 1) >= 4'd0) && ((Boo_ba1 << 1) <= 4'd1)
    );

    // The SubB contribution is always zero or one.
    check_subb_contribution_range: assert property (
        @(posedge clk)
        ((Boo_ba2 + b) >= 4'd0) && ((Boo_ba2 + b) <= 4'd1)
    );

    // The SubC contribution is always zero or one.
    check_subc_contribution_range: assert property (
        @(posedge clk)
        ((Boo_ba3 - c) >= 4'd0) && ((Boo_ba3 - c) <= 4'd1)
    );

    // If all three submodules' contributions are zero, f4 is zero.
    check_all_zero_case: assert property (
        @(posedge clk)
        ((Boo_ba1 << 1) == 4'd0) && ((Boo_ba2 + b) == 4'd0) && ((Boo_ba3 - c) == 4'd0)
        |-> (f4_dotnamed == 4'd0)
    );

    // If all three submodules' contributions are one, f4 is three.
    check_all_one_case: assert property (
        @(posedge clk)
        ((Boo_ba1 << 1) == 4'd1) && ((Boo_ba2 + b) == 4'd1) && ((Boo_ba3 - c) == 4'd1)
        |-> (f4_dotnamed == 4'd3)
    );

    // If the SubB and SubC contributions are zero, f4 equals the SubA contribution.
    check_subb_subc_zero_case: assert property (
        @(posedge clk)
        ((Boo_ba2 + b) == 4'd0) && ((Boo_ba3 - c) == 4'd0)
        |-> (f4_dotnamed == (Boo_ba1 << 1))
    );

    // If the SubA and SubC contributions are zero, f4 equals the SubB contribution.
    check_suba_subc_zero_case: assert property (
        @(posedge clk)
        ((Boo_ba1 << 1) == 4'd0) && ((Boo_ba3 - c) == 4'd0)
        |-> (f4_dotnamed == (Boo_ba2 + b))
    );

    // If the SubA and SubB contributions are zero, f4 equals the SubC contribution.
    check_suba_subb_zero_case: assert property (
        @(posedge clk)
        ((Boo_ba1 << 1) == 4'd0) && ((Boo_ba2 + b) == 4'd0)
        |-> (f4_dotnamed == (Boo_ba3 - c))
    );

endmodule