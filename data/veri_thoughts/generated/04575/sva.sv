module final_module_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [7:0] DATA_IN,
    input logic LOAD,
    input logic SHIFT,
    input logic [2:0] op,
    input logic clk,
    input logic reset,
    input logic [3:0] Z,
    input logic [3:0] alu_out,
    input logic [3:0] shift_out,
    input logic [3:0] and_out
);

    function automatic logic [3:0] alu_expected (
        input logic [3:0] a,
        input logic [3:0] b,
        input logic [2:0] oper
    );
        begin
            case (oper)
                3'b000: alu_expected = a + b;
                3'b001: alu_expected = a - b;
                3'b010: alu_expected = a & b;
                3'b011: alu_expected = a | b;
                3'b100: alu_expected = a ^ b;
                3'b101: alu_expected = ~a;
                default: alu_expected = 4'b0000;
            endcase
        end
    endfunction

    // ALU adds A and B for op 000.
    check_alu_add: assert property (
        @(posedge clk) disable iff (reset)
        (op == 3'b000) |-> (alu_out == alu_expected(A, B, 3'b000))
    );

    // ALU subtracts B from A for op 001.
    check_alu_sub: assert property (
        @(posedge clk) disable iff (reset)
        (op == 3'b001) |-> (alu_out == alu_expected(A, B, 3'b001))
    );

    // ALU computes bitwise AND for op 010.
    check_alu_and: assert property (
        @(posedge clk) disable iff (reset)
        (op == 3'b010) |-> (alu_out == alu_expected(A, B, 3'b010))
    );

    // ALU computes bitwise OR for op 011.
    check_alu_or: assert property (
        @(posedge clk) disable iff (reset)
        (op == 3'b011) |-> (alu_out == alu_expected(A, B, 3'b011))
    );

    // ALU computes bitwise XOR for op 100.
    check_alu_xor: assert property (
        @(posedge clk) disable iff (reset)
        (op == 3'b100) |-> (alu_out == alu_expected(A, B, 3'b100))
    );

    // ALU computes bitwise NOT of A for op 101.
    check_alu_not: assert property (
        @(posedge clk) disable iff (reset)
        (op == 3'b101) |-> (alu_out == alu_expected(A, B, 3'b101))
    );

    // ALU drives zero for unsupported op values.
    check_alu_default_zero: assert property (
        @(posedge clk) disable iff (reset)
        ((op == 3'b110) || (op == 3'b111)) |-> (alu_out == 4'b0000)
    );

    // and_out is the bitwise AND of alu_out and shift_out.
    check_and_out_logic: assert property (
        @(posedge clk) disable iff (reset)
        (and_out == (alu_out & shift_out))
    );

    // LOAD copies DATA_IN[3:0] into the shift register and overrides SHIFT.
    check_shift_load_priority: assert property (
        @(posedge clk) disable iff (reset)
        LOAD |=> (shift_out == $past(DATA_IN[3:0]))
    );

    // SHIFT moves the register left and inserts 0 when LOAD is low.
    check_shift_left: assert property (
        @(posedge clk) disable iff (reset)
        (!LOAD && SHIFT) |=> (shift_out == {$past(shift_out[2:0]), 1'b0})
    );

    // The shift register holds its value when LOAD and SHIFT are both low.
    check_shift_hold: assert property (
        @(posedge clk) disable iff (reset)
        (!LOAD && !SHIFT) |=> (shift_out == $past(shift_out))
    );

    // Synchronous active-high reset clears Z on the next clock.
    check_z_synchronous_reset: assert property (
        @(posedge clk)
        reset |=> (Z == 4'b0000)
    );

    // Without reset, Z captures the previous cycle and_out.
    check_z_captures_and_out: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (Z == $past(and_out))
    );

endmodule