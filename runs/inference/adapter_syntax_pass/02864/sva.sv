module mux2_sva (
    input logic clk,
    input logic sel,
    input logic in1,
    input logic in2,
    input logic out
);

    // When sel is low, out captures in1 on the next clock.
    check_sel_low_captures_in1: assert property (
        @(posedge clk) (sel === 1'b0) |=> (out === $past(in1))
    );

    // When sel is high, out captures in2 on the next clock.
    check_sel_high_captures_in2: assert property (
        @(posedge clk) (sel === 1'b1) |=> (out === $past(in2))
    );

    // If both inputs are equal, out matches that common value on the next clock.
    check_equal_inputs_passthrough: assert property (
        @(posedge clk) (in1 === in2) |=> (out === $past(in1))
    );

endmodule