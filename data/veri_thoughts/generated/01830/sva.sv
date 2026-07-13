module alu_sva (
    input logic CLK,
    input logic [3:0] ctl,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [31:0] out,
    input logic zero
);
    // Local re-computation of internal RTL wires for checking
    logic [31:0] add_ab, sub_ab;
    logic oflow_sub;
    logic slt;

    assign add_ab   = a + b;
    assign sub_ab   = a - b;
    assign oflow_sub = (a[31] == b[31]) && (sub_ab[31] != a[31]);
    assign slt      = oflow_sub ? ~a[31] : a[31];

    // zero output equals (out == 0)
    check_zero_definition: assert property (
        @(posedge CLK) zero == (out == 32'd0)
    );

    // ADD opcode: out equals a + b
    check_add_result: assert property (
        @(posedge CLK) (ctl == 4'b0010) |-> (out == add_ab)
    );

    // SUB opcode: out equals a - b
    check_sub_result: assert property (
        @(posedge CLK) (ctl == 4'b0110) |-> (out == sub_ab)
    );

    // AND opcode: out equals a & b
    check_and_result: assert property (
        @(posedge CLK) (ctl == 4'b0000) |-> (out == (a & b))
    );

    // OR opcode: out equals a | b
    check_or_result: assert property (
        @(posedge CLK) (ctl == 4'b0001) |-> (out == (a | b))
    );

    // NOR opcode: out equals ~(a | b)
    check_nor_result: assert property (
        @(posedge CLK) (ctl == 4'b1100) |-> (out == ~(a | b))
    );

    // XOR opcode: out equals a ^ b
    check_xor_result: assert property (
        @(posedge CLK) (ctl == 4'b1101) |-> (out == (a ^ b))
    );

    // SLT opcode: LSB equals slt
    check_slt_lsb: assert property (
        @(posedge CLK) (ctl == 4'b0111) |-> (out[0] == slt)
    );

    // SLT opcode: upper 31 bits are zero
    check_slt_upper_zero: assert property (
        @(posedge CLK) (ctl == 4'b0111) |-> (out[31:1] == 31'd0)
    );

    // Default opcode: out equals zero for unlisted ctl values
    check_default_zero: assert property (
        @(posedge CLK) !(ctl inside {4'b0010,4'b0000,4'b1100,4'b0001,4'b0111,4'b0110,4'b1101}) |-> (out == 32'd0)
    );
endmodule