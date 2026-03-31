module top_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic f
);

    // f is always high.
    check_f_always_high: assert property (
        @(posedge clk) f == 1'b1
    );

    // f is high when a and b are equal.
    check_f_high_when_inputs_equal: assert property (
        @(posedge clk) (a == b) |-> (f == 1'b1)
    );

    // f is high when a and b are different.
    check_f_high_when_inputs_different: assert property (
        @(posedge clk) (a != b) |-> (f == 1'b1)
    );

    // f is high when the mux selects the 00 input.
    check_f_high_when_mux_selects_00: assert property (
        @(posedge clk) ((a == b) && (a == 1'b0)) |-> (f == 1'b1)
    );

    // f is high when the mux selects the 01 input.
    check_f_high_when_mux_selects_01: assert property (
        @(posedge clk) ((a != b) && (a == 1'b0)) |-> (f == 1'b1)
    );

    // f is high when the mux selects the 10 input.
    check_f_high_when_mux_selects_10: assert property (
        @(posedge clk) ((a == b) && (a == 1'b1)) |-> (f == 1'b1)
    );

    // f is high when the mux selects the 11 input.
    check_f_high_when_mux_selects_11: assert property (
        @(posedge clk) ((a != b) && (a == 1'b1)) |-> (f == 1'b1)
    );

endmodule