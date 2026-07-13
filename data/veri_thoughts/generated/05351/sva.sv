module top_module_assertions (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic enable,
    input logic EQ,
    input logic GT,
    input logic OR
);

    // No reset in RTL; sample combinational behavior on clk.

    // EQ matches the selected input compared against B.
    check_eq_function: assert property (
        @(posedge clk) EQ == (enable ? 1'b1 : (A == B))
    );

    // GT matches the selected input compared against B.
    check_gt_function: assert property (
        @(posedge clk) GT == (enable ? 1'b0 : (A > B))
    );

    // OR is the OR of the comparator outputs.
    check_or_combination: assert property (
        @(posedge clk) OR == (EQ | GT)
    );

    // EQ and GT cannot both be high at the same time.
    check_compare_mutex: assert property (
        @(posedge clk) !(EQ && GT)
    );

    // When enable is high, the mux selects B so the compare is B vs B.
    check_enable_selects_b: assert property (
        @(posedge clk) enable |-> (EQ && !GT && OR)
    );

    // When enable is low and A is less than B, all compare outputs are low.
    check_disable_less_than_case: assert property (
        @(posedge clk) (!enable && (A < B)) |-> (!EQ && !GT && !OR)
    );

    // When enable is low and A equals B, EQ and OR are high and GT is low.
    check_disable_equal_case: assert property (
        @(posedge clk) (!enable && (A == B)) |-> (EQ && !GT && OR)
    );

    // When enable is low and A is greater than B, GT and OR are high and EQ is low.
    check_disable_greater_than_case: assert property (
        @(posedge clk) (!enable && (A > B)) |-> (!EQ && GT && OR)
    );

endmodule