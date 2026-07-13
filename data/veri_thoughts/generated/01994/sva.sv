module adder_8bit_sva (
    input  logic        clk,
    input  logic [7:0]  input_a,
    input  logic [7:0]  input_b,
    input  logic [7:0]  output_c
);
    // Output equals sum of inputs from the previous cycle (1-cycle latency).
    check_sum_pipeline: assert property (
        @(posedge clk) output_c == $past(input_a + input_b)
    );

    // If previous A was zero, output equals previous B.
    check_sum_with_zero_a: assert property (
        @(posedge clk) ($past(input_a) == 8'h00) |-> (output_c == $past(input_b))
    );

    // If previous B was zero, output equals previous A.
    check_sum_with_zero_b: assert property (
        @(posedge clk) ($past(input_b) == 8'h00) |-> (output_c == $past(input_a))
    );

    // LSB of output equals XOR of previous-cycle LSBs (no carry-in).
    check_lsb_xor: assert property (
        @(posedge clk) output_c[0] == $past(input_a[0] ^ input_b[0])
    );

    // If inputs were unchanged across two prior cycles, output holds its value.
    check_output_stable_when_inputs_unchanged: assert property (
        @(posedge clk) (($past(input_a,1) == $past(input_a,2)) && ($past(input_b,1) == $past(input_b,2))) |-> (output_c == $past(output_c))
    );

    // Wraparound example: 0xFF + 0x01 (prev cycle) produces 0x00.
    check_wrap_ff_plus_01: assert property (
        @(posedge clk) (($past(input_a) == 8'hFF) && ($past(input_b) == 8'h01)) |-> (output_c == 8'h00)
    );

    // Wraparound example: 0xFF + 0xFF (prev cycle) produces 0xFE.
    check_wrap_ff_plus_ff: assert property (
        @(posedge clk) (($past(input_a) == 8'hFF) && ($past(input_b) == 8'hFF)) |-> (output_c == 8'hFE)
    );

    // If previous inputs were equal, output equals previous A doubled (mod 256).
    check_doubling_when_equal_inputs: assert property (
        @(posedge clk) ($past(input_a) == $past(input_b)) |-> (output_c == ($past(input_a) << 1))
    );

    // Swapping inputs across two consecutive cycles keeps the output the same.
    check_commutativity_swap_preserves_output: assert property (
        @(posedge clk) (($past(input_a,1) == $past(input_b,2)) && ($past(input_b,1) == $past(input_a,2))) |-> (output_c == $past(output_c))
    );
endmodule