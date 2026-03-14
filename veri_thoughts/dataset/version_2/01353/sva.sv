module demux_1to256_pipeline_sva (
    input logic clk,
    input logic [31:0] in,
    input logic [7:0] out
);
    // Next-cycle out equals previous in[0] replicated to 8 bits.
    check_out_eq_prev_in0_rep: assert property (
        @(posedge clk) 1'b1 |=> (out == {8{$past(in[0])}})
    );

    // Next-cycle out has all bits identical.
    check_out_next_bits_identical: assert property (
        @(posedge clk) 1'b1 |=> (out == {8{out[0]}})
    );

    // Next-cycle out is either 8'h00 or 8'hFF.
    check_out_next_is_00_or_FF: assert property (
        @(posedge clk) 1'b1 |=> ((out == 8'h00) || (out == 8'hFF))
    );

    // Rising in[0] produces 8'hFF on out next cycle.
    check_in0_rise_sets_out_ones: assert property (
        @(posedge clk) $rose(in[0]) |=> (out == 8'hFF)
    );

    // Falling in[0] produces 8'h00 on out next cycle.
    check_in0_fall_clears_out_zero: assert property (
        @(posedge clk) $fell(in[0]) |=> (out == 8'h00)
    );

    // If in[0] is stable over a cycle, out is stable over the next cycle.
    check_stable_in0_keeps_out_stable: assert property (
        @(posedge clk) (in[0] == $past(in[0])) |-> (out == $past(out))
    );

    // If in[0] changes over a cycle, out changes on the next cycle.
    check_change_in0_changes_out: assert property (
        @(posedge clk) (in[0] != $past(in[0])) |-> (out != $past(out))
    );

    // If out is 8'hFF now, in[0] was 1 in the previous cycle.
    check_out_ff_implies_prev_in1: assert property (
        @(posedge clk) (out == 8'hFF) |-> ($past(in[0]) == 1'b1)
    );

    // If out is 8'h00 now, in[0] was 0 in the previous cycle.
    check_out_00_implies_prev_in0: assert property (
        @(posedge clk) (out == 8'h00) |-> ($past(in[0]) == 1'b0)
    );
endmodule