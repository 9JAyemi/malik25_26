module reverse_last_two_bits_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [1:0] out
);

    // Output is the previous cycle's concatenation of input bits [1:0] and [3:2].
    check_output_matches_previous_input: assert property (
        @(posedge clk) disable iff ($initstate)
        out == {$past(in[1:0]), $past(in[3:2])}
    );

    // Output bit 0 comes from the previous cycle's input bit 1.
    check_output_bit0_from_prev_in1: assert property (
        @(posedge clk) disable iff ($initstate)
        out[0] == $past(in[1])
    );

    // Output bit 1 comes from the previous cycle's input bit 3.
    check_output_bit1_from_prev_in3: assert property (
        @(posedge clk) disable iff ($initstate)
        out[1] == $past(in[3])
    );

    // Output equals the previous cycle's {in[1:0], in[3:2]}.
    check_output_vector_from_previous_input: assert property (
        @(posedge clk) disable iff ($initstate)
        out == {$past(in[1:0]), $past(in[3:2])}
    );

    // If the previous cycle's input was stable, the output remains stable.
    check_output_stable_when_previous_input_stable: assert property (
        @(posedge clk) disable iff ($initstate)
        $stable($past(in)) |-> $stable(out)
    );

    // If the previous cycle's input changed, the output changes.
    check_output_changes_when_previous_input_changes: assert property (
        @(posedge clk) disable iff ($initstate)
        !$stable($past(in)) |-> !$stable(out)
    );

endmodule