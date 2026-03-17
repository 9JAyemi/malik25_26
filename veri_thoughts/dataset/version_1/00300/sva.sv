module edge_detector_sva (
    input logic clk,
    input logic [7:0] in,
    input logic [7:0] anyedge
);

    // Upper bits shift forward by one position each cycle.
    check_anyedge_shift_upper: assert property (
        @(posedge clk) disable iff ($initstate)
        anyedge[7:1] == $past(anyedge[6:0])
    );

    // An input change shifts a 1 into the register on the next cycle.
    check_change_shifts_in_one: assert property (
        @(posedge clk) disable iff ($initstate)
        (in != $past(in)) |=> (anyedge == {$past(anyedge[6:0]), 1'b1})
    );

    // A stable input shifts a 0 into the register on the next cycle.
    check_stable_shifts_in_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        (in == $past(in)) |=> (anyedge == {$past(anyedge[6:0]), 1'b0})
    );

    // An input change sets the next-cycle LSB.
    check_change_sets_lsb: assert property (
        @(posedge clk) disable iff ($initstate)
        (in != $past(in)) |=> (anyedge[0] == 1'b1)
    );

    // A stable input clears the next-cycle LSB.
    check_stable_clears_lsb: assert property (
        @(posedge clk) disable iff ($initstate)
        (in == $past(in)) |=> (anyedge[0] == 1'b0)
    );

endmodule