module components_dff_en_rst_sva #(
    parameter WIDTH = 1,
    parameter RESET_VAL = 0
) (
    input logic clk,
    input logic rst,
    input logic en,
    input logic [WIDTH-1:0] d,
    input logic [WIDTH-1:0] q
);

    // Reset loads the output to RESET_VAL on the next clock.
    check_reset_loads_q: assert property (
        @(posedge clk) rst |=> (q == RESET_VAL)
    );

    // Reset has priority over enable when both are asserted.
    check_reset_priority_over_enable: assert property (
        @(posedge clk) (rst && en) |=> (q == RESET_VAL)
    );

    // With reset low and enable high, the output captures d.
    check_enable_captures_d: assert property (
        @(posedge clk) disable iff (rst) en |=> (q == $past(d))
    );

    // With reset low and enable low, the output holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (rst) !en |=> (q == $past(q))
    );

endmodule

module components_dff_en_sva #(
    parameter WIDTH = 1
) (
    input logic clk,
    input logic en,
    input logic [WIDTH-1:0] d,
    input logic [WIDTH-1:0] q
);

    // With enable high, the output captures d on the next clock.
    check_enable_captures_d: assert property (
        @(posedge clk) en |=> (q == $past(d))
    );

    // With enable low, the output holds its value on the next clock.
    check_hold_when_disabled: assert property (
        @(posedge clk) !en |=> (q == $past(q))
    );

endmodule

module components_dff_sva #(
    parameter WIDTH = 1
) (
    input logic clk,
    input logic [WIDTH-1:0] d,
    input logic [WIDTH-1:0] q
);

    // The output captures d on the next clock.
    check_capture_d: assert property (
        @(posedge clk) 1'b1 |=> (q == $past(d))
    );

endmodule