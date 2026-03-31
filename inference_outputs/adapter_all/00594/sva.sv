module top_module_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic        select,
    input logic [31:0] sum
);

    // When select is low, sum must be the zero-extended mux output.
    check_select_low_path: assert property (
        @(posedge clk) (select == 1'b0) |-> (sum == {31'b0, a[0]})
    );

    // When select is high, sum must be the zero-extended adder output.
    check_select_high_path: assert property (
        @(posedge clk) (select == 1'b1) |-> (sum == {30'b0, a[31:1]})
    );

    // With select low and a[0] low, sum must be zero.
    check_select_low_zero: assert property (
        @(posedge clk) (select == 1'b0 && a[0] == 1'b0) |-> (sum == 32'b0)
    );

    // With select low and a[0] high, sum must be one.
    check_select_low_one: assert property (
        @(posedge clk) (select == 1'b0 && a[0] == 1'b1) |-> (sum == 32'h00000001)
    );

    // With select high and a[31:1] zero, sum must be zero.
    check_select_high_zero: assert property (
        @(posedge clk) (select == 1'b1 && a[31:1] == 31'b0) |-> (sum == 32'b0)
    );

    // With select high and a[31:1] nonzero, sum must be all ones.
    check_select_high_one: assert property (
        @(posedge clk) (select == 1'b1 && a[31:1] != 31'b0) |-> (sum == 32'hFFFF_FFFF)
    );

    // With select high and a[31:1] zero, sum must be zero.
    check_select_high_zero: assert property (
        @(posedge clk) (select == 1'b1 && a[31:1] == 31'b0) |-> (sum == 32'b0)
    );

    // With select high and a[31:1] nonzero, sum must be all ones.
    check_select_high_one: assert property (
        @(posedge clk) (select == 1'b1 && a[31:1] != 31'b0) |-> (sum == 32'hFFFF_FFFF)
    );

    // With select high and a[31:1] zero, sum must be zero.
    check_select_high_zero: assert property (
        @(posedge clk) (select == 1'b1 && a[31:1] == 31'b0) |-> (sum == 32'b0)
    );

    // With select high and a[31:1] nonzero, sum must be all ones.
    check_select_high_one: assert property (
        @(posedge clk) (select == 1'b1 && a[31:1] != 31'b0) |-> (sum == 32'hFFFF_FFFF)
    );

endmodule