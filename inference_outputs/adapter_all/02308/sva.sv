module nand2_module_sva (
    input logic in1,
    input logic in2,
    input logic clk,
    input logic out
);

    // Output reflects the NAND of the two inputs from the previous clock.
    check_registered_nand: assert property (
        @(posedge clk) disable iff ($initstate)
        out == ~($past(in1) & $past(in2))
    );

    // If both inputs were high on the previous clock, the output is low.
    check_prev_high_high_drives_low: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(in1) && $past(in2)) |-> (out == 1'b0)
    );

    // If either input was low on the previous clock, the output is high.
    check_prev_any_low_drives_high: assert property (
        @(posedge clk) disable iff ($initstate)
        (!$past(in1) || !$past(in2)) |-> (out == 1'b1)
    );

    // A low output means both inputs were high on the previous clock.
    check_low_output_implies_prev_high_high: assert property (
        @(posedge clk) disable iff ($initstate)
        (out == 1'b0) |-> ($past(in1) && $past(in2))
    );

    // A high output means at least one input was low on the previous clock.
    check_high_output_implies_prev_any_low: assert property (
        @(posedge clk) disable iff ($initstate)
        (out == 1'b1) |-> (!$past(in1) || !$past(in2))
    );

endmodule