module barrel_shifter_sva (
    input logic clk,
    input logic [3:0] data_in,
    input logic [1:0] control,
    input logic [3:0] data_out
);
    // Clock: none in RTL; assertions use external clk. Reset: none. Logic: purely combinational.

    // control=00: logical left shift by 1 with zero fill.
    check_sll_result: assert property (
        @(posedge clk) disable iff (1'b0) (control == 2'b00) |-> (data_out == {data_in[2:0], 1'b0})
    );

    // control=01: logical right shift by 1 with zero fill.
    check_srl_result: assert property (
        @(posedge clk) disable iff (1'b0) (control == 2'b01) |-> (data_out == {1'b0, data_in[3:1]})
    );

    // control=10: rotate left by 1.
    check_rol_result: assert property (
        @(posedge clk) disable iff (1'b0) (control == 2'b10) |-> (data_out == {data_in[2:0], data_in[3]})
    );

    // control=11: arithmetic right shift by 1 (sign extension).
    check_asr_result: assert property (
        @(posedge clk) disable iff (1'b0) (control == 2'b11) |-> (data_out == {data_in[3], data_in[3:1]})
    );

    // For SLL (00), LSB must be zero (zero-fill).
    check_sll_zero_lsb: assert property (
        @(posedge clk) disable iff (1'b0) (control == 2'b00) |-> (data_out[0] == 1'b0)
    );

    // For SRL (01), MSB must be zero (zero-fill).
    check_srl_zero_msb: assert property (
        @(posedge clk) disable iff (1'b0) (control == 2'b01) |-> (data_out[3] == 1'b0)
    );

    // For ROL (10), LSB equals prior MSB.
    check_rol_lsb_is_msb: assert property (
        @(posedge clk) disable iff (1'b0) (control == 2'b10) |-> (data_out[0] == data_in[3])
    );

    // For ASR (11), MSB equals sign bit.
    check_asr_msb_is_sign: assert property (
        @(posedge clk) disable iff (1'b0) (control == 2'b11) |-> (data_out[3] == data_in[3])
    );

    // For ASR (11), bit2 equals sign bit after shift.
    check_asr_bit2_is_sign: assert property (
        @(posedge clk) disable iff (1'b0) (control == 2'b11) |-> (data_out[2] == data_in[3])
    );

    // If inputs are stable, output must remain stable (combinational determinism).
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (1'b0) ($stable(control) && $stable(data_in)) |-> $stable(data_out)
    );
endmodule