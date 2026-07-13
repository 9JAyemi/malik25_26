module data_modifier_sva (
    input logic        clk,
    input logic [31:0] reg_input,
    input logic [3:0]  address,
    input logic        reg_out_syn,
    input logic        ack,
    input logic        ack_syn,
    input logic [31:0] reg_out
);

    // Sampled on external clk because the RTL has no clock or reset.

    // ack=1 and ack_syn=0 selects a left shift by one bit.
    check_left_shift: assert property (
        @(posedge clk)
        $stable({reg_input, ack, ack_syn}) && ack && !ack_syn
        |-> reg_out == {reg_input[30:0], 1'b0}
    );

    // ack=0 and ack_syn=1 selects a right shift by one bit.
    check_right_shift: assert property (
        @(posedge clk)
        $stable({reg_input, ack, ack_syn}) && !ack && ack_syn
        |-> reg_out == {1'b0, reg_input[31:1]}
    );

    // ack=1 and ack_syn=1 selects the byte-reversed value.
    check_byte_reverse: assert property (
        @(posedge clk)
        $stable({reg_input, ack, ack_syn}) && ack && ack_syn
        |-> reg_out == {reg_input[7:0], reg_input[15:8], reg_input[23:16], reg_input[31:24]}
    );

    // ack=0 and ack_syn=0 passes reg_input through unchanged.
    check_passthrough: assert property (
        @(posedge clk)
        $stable({reg_input, ack, ack_syn}) && !ack && !ack_syn
        |-> reg_out == reg_input
    );

    // Stable data and control inputs keep reg_out stable.
    check_output_stable_for_stable_inputs: assert property (
        @(posedge clk)
        $stable({reg_input, ack, ack_syn})
        |-> $stable(reg_out)
    );

    // Changing address alone does not affect reg_out.
    check_address_no_effect: assert property (
        @(posedge clk)
        $changed(address) && $stable({reg_input, ack, ack_syn})
        |-> $stable(reg_out)
    );

    // Changing reg_out_syn alone does not affect reg_out.
    check_reg_out_syn_no_effect_on_reg_out: assert property (
        @(posedge clk)
        $changed(reg_out_syn) && $stable({reg_input, ack, ack_syn})
        |-> $stable(reg_out)
    );

endmodule