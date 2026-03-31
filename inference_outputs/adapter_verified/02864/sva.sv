module mux2_sva (
    input logic clk,
    input logic sel,
    input logic in1,
    input logic in2,
    input logic out
);

// When sel is 0, out captures in1 on the next clock.
    check_sel0_captures_in1: assert property (
        @(posedge clk) (sel == 1'b0) |=> (out == $past(in1))
    );

// When sel is 1, out captures in2 on the next clock.
    check_sel1_captures_in2: assert property (
        @(posedge clk) (sel == 1'b1) |=> (out == $past(in2))
    );

// If both inputs are equal, out matches that value on the next clock.
    check_equal_inputs_match: assert property (
        @(posedge clk) (in1 == in2) |=> (out == $past(in1))
    );

// If sel toggles between consecutive clocks, out follows the current select.
    check_toggle_follows_sel: assert property (
        @(posedge clk) $past(sel) != sel |=> (out == ($past(sel) ? $past(in2) : $past(in1)))
    );

endmodule
