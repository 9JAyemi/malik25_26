module nios_system_alu_sva (
    input logic        clk,
    input logic        reset_n,
    input logic [31:0] in_data,
    input logic [2:0]  op_select,
    input logic        enable,
    input logic [31:0] out_data
);

    // A sampled reset cycle clears the output by the next clock.
    check_reset_clears_output: assert property (
        @(posedge clk) !reset_n |=> (out_data == 32'd0)
    );

    // When disabled, the registered output holds its prior value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (!reset_n)
        (!enable) |=> (out_data == $past(out_data))
    );

    // AND opcode writes in_data & in_data on the next clock.
    check_and_operation: assert property (
        @(posedge clk) disable iff (!reset_n)
        (enable && (op_select == 3'b000)) |=> (out_data == $past(in_data & in_data))
    );

    // OR opcode writes in_data | in_data on the next clock.
    check_or_operation: assert property (
        @(posedge clk) disable iff (!reset_n)
        (enable && (op_select == 3'b001)) |=> (out_data == $past(in_data | in_data))
    );

    // XOR opcode writes in_data ^ in_data on the next clock.
    check_xor_operation: assert property (
        @(posedge clk) disable iff (!reset_n)
        (enable && (op_select == 3'b010)) |=> (out_data == $past(in_data ^ in_data))
    );

    // NOT opcode writes ~in_data on the next clock.
    check_not_operation: assert property (
        @(posedge clk) disable iff (!reset_n)
        (enable && (op_select == 3'b011)) |=> (out_data == $past(~in_data))
    );

    // ADD opcode writes in_data + in_data on the next clock.
    check_add_operation: assert property (
        @(posedge clk) disable iff (!reset_n)
        (enable && (op_select == 3'b100)) |=> (out_data == $past(in_data + in_data))
    );

    // SUB opcode writes in_data - in_data on the next clock.
    check_sub_operation: assert property (
        @(posedge clk) disable iff (!reset_n)
        (enable && (op_select == 3'b101)) |=> (out_data == $past(in_data - in_data))
    );

    // MUL opcode writes in_data * in_data on the next clock.
    check_mul_operation: assert property (
        @(posedge clk) disable iff (!reset_n)
        (enable && (op_select == 3'b110)) |=> (out_data == $past(in_data * in_data))
    );

    // DIV opcode writes in_data / in_data on the next clock for nonzero input.
    check_div_operation_nonzero: assert property (
        @(posedge clk) disable iff (!reset_n)
        (enable && (op_select == 3'b111) && (in_data != 32'd0)) |=> (out_data == $past(in_data / in_data))
    );

endmodule