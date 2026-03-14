module nand_decoder_sva (
    input logic clk,
    input logic rst_n,
    input logic [1:0] in,
    input logic [3:0] out
);
    // All 4 outputs equal the AND of the two inputs.
    check_out_matches_and_broadcast: assert property (
        @(posedge clk) disable iff (!rst_n) out == {4{in[0] & in[1]}}
    );

    // All output bits are identical at all times.
    check_all_outs_equal: assert property (
        @(posedge clk) disable iff (!rst_n) (out[0] == out[1]) && (out[1] == out[2]) && (out[2] == out[3])
    );

    // Outputs are all zero when any input is zero.
    check_out_zero_when_any_input_zero: assert property (
        @(posedge clk) disable iff (!rst_n) ((!in[0]) || (!in[1])) |-> (out == 4'b0000)
    );

    // Outputs are all one when both inputs are one.
    check_out_one_when_both_inputs_one: assert property (
        @(posedge clk) disable iff (!rst_n) (in[0] && in[1]) |-> (out == 4'b1111)
    );

    // A rising edge on any output implies both inputs are one.
    check_out_rise_implies_inputs_high: assert property (
        @(posedge clk) disable iff (!rst_n) $rose(out[0]) |-> (in[0] && in[1])
    );

    // A falling edge on any output implies at least one input is zero.
    check_out_fall_implies_any_input_low: assert property (
        @(posedge clk) disable iff (!rst_n) $fell(out[0]) |-> ((!in[0]) || (!in[1]))
    );

    // With stable inputs between cycles, outputs remain stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (!rst_n) ($past(in) === in) |-> ($past(out) === out)
    );

    // Output bus can only be all-zeros or all-ones.
    check_out_is_const_bus: assert property (
        @(posedge clk) disable iff (!rst_n) (out == 4'b0000) || (out == 4'b1111)
    );
endmodule