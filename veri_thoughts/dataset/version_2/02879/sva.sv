module four_input_module_sva (
    // DUT ports
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic y,
    // Sampling clock for assertions (DUT has no clock/reset)
    input logic CLK
);
    // y implements y = (a&b&c&d) | (!a & !b & !c & !d).
    check_y_functional_equivalence: assert property (
        @(posedge CLK) y == ((a & b & c & d) | (!a & !b & !c & !d))
    );

    // If all inputs are 1, y must be 1.
    check_y_true_on_all_ones: assert property (
        @(posedge CLK) (a & b & c & d) |-> (y == 1'b1)
    );

    // If all inputs are 0, y must be 1.
    check_y_true_on_all_zeros: assert property (
        @(posedge CLK) (!a & !b & !c & !d) |-> (y == 1'b1)
    );

    // If inputs are mixed (not all 1s or all 0s), y must be 0.
    check_y_false_on_mixed: assert property (
        @(posedge CLK) (!((a & b & c & d) || (!a & !b & !c & !d))) |-> (y == 1'b0)
    );

    // If y is 1, inputs must be all 1s or all 0s.
    check_y_one_implies_extremes: assert property (
        @(posedge CLK) (y == 1'b1) |-> ((a & b & c & d) || (!a & !b & !c & !d))
    );
endmodule