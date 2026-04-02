module xor_shift_register_sva (
    input logic clk,
    input logic load,
    input logic [1:0] ena,
    input logic [99:0] data,
    output logic [99:0] q,
    output logic out_if_else
);
    // Sequential logic: shift_reg is updated on the rising edge of clk
    // Load signal updates shift_reg with data
    load_shift_reg: assert property (
        @(posedge clk) disable iff (!load) shift_reg == data
    );

    // Sequential logic: shift_reg is updated on the rising edge of clk
    // When ena is not 00, shift_reg is circularly shifted right by 1 bit
    shift_reg_update: assert property (
        @(posedge clk) disable iff (!ena) shift_reg == {shift_reg[98:0], shift_reg[99]}
    );

    // Combinational logic: out_if_else is assigned based on the XOR of shift_reg and data
    out_if_else_assignment: assert property (
        @(posedge clk) disable iff (!ena) out_if_else == (shift_reg ^ data)
    );

    // Combinational logic: q is assigned the value of shift_reg
    q_assignment: assert property (
        @(posedge clk) disable iff (!ena) q == shift_reg
    );
endmodule