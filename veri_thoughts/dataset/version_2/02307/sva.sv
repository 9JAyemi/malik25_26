module edge_detector_sva (
    input logic clk,
    input logic [7:0] in,
    input logic [7:0] anyedge
);
    // Clock: clk (posedge). Reset: none in RTL.
    // Sequential logic: samples in; anyedge=8'h01 on change, else 8'h00. Bits [7:1] always 0.

    // anyedge must be either 8'h00 or 8'h01 each cycle.
    check_anyedge_valid_values: assert property (
        @(posedge clk) (anyedge == 8'h00) || (anyedge == 8'h01)
    );

    // Upper bits of anyedge are always zero.
    check_anyedge_upper_bits_zero: assert property (
        @(posedge clk) anyedge[7:1] == 7'b0
    );

    // LSB of anyedge equals the change flag between current and previous in.
    check_lsb_matches_change: assert property (
        @(posedge clk) disable iff ($initstate) anyedge[0] == (in != $past(in))
    );

    // When input changes from previous cycle, anyedge must be 8'h01.
    check_anyedge_when_input_changes: assert property (
        @(posedge clk) disable iff ($initstate) (in != $past(in)) |-> (anyedge == 8'h01)
    );

    // When input is unchanged from previous cycle, anyedge must be 8'h00.
    check_anyedge_when_input_unchanged: assert property (
        @(posedge clk) disable iff ($initstate) (in == $past(in)) |-> (anyedge == 8'h00)
    );

endmodule