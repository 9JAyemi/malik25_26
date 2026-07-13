module alu_sva (
    input logic CLK,
    input logic RESETn,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [4:0] aluc,
    output logic [31:0] result
);
    // Addition (signed)
    add_signed: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd0) |-> (result == a + b)
    );
    // Addition (unsigned)
    add_unsigned: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd1) |-> (result == a + b)
    );
    // Subtraction (signed)
    sub_signed: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd2) |-> (result == a - b)
    );
    // Subtraction (unsigned)
    sub_unsigned: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd3) |-> (result == a - b)
    );
    // Bitwise AND
    bitwise_and: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd4) |-> (result == a & b)
    );
    // Bitwise OR
    bitwise_or: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd5) |-> (result == a | b)
    );
    // Bitwise XOR
    bitwise_xor: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd6) |-> (result == a ^ b)
    );
    // Bitwise NOR
    bitwise_nor: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd7) |-> (result == ~(a | b))
    );
    // Set Less Than (signed)
    set_less_than_signed: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd8) |-> (result == (a[31]^b[31])?(a[31]?1:0):(a<b))
    );
    // Set Less Than (unsigned)
    set_less_than_unsigned: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd9) |-> (result == a < b)
    );
    // Shift Left Logical
    shift_left_logical: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd10) |-> (result == b << a)
    );
    // Shift Right Logical
    shift_right_logical: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd11) |-> (result == b >> a)
    );
    // Shift Right Arithmetic
    shift_right_arithmetic: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd12) |-> (result == $signed(b) >>> a)
    );
    // Load Upper Immediate
    load_upper_immediate: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd14) |-> (result == {b[15:0], 16'b0})
    );
    // Zero
    zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd31) |-> (result == 0)
    );
endmodule