module alu_assertions (
    input logic       clk,
    input logic [3:0] op,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] y,
    input logic       cin,
    input logic       cout,
    input logic       zout
);

    localparam [3:0] ALUOP_ADD  = 4'b0000;
    localparam [3:0] ALUOP_SUB  = 4'b1000;
    localparam [3:0] ALUOP_AND  = 4'b0001;
    localparam [3:0] ALUOP_OR   = 4'b0010;
    localparam [3:0] ALUOP_XOR  = 4'b0011;
    localparam [3:0] ALUOP_COM  = 4'b0100;
    localparam [3:0] ALUOP_ROR  = 4'b0101;
    localparam [3:0] ALUOP_ROL  = 4'b0110;
    localparam [3:0] ALUOP_SWAP = 4'b0111;

    // ADD returns the 8-bit sum and carry-out.
    check_add_result: assert property (
        @(posedge clk)
        (op == ALUOP_ADD) |-> ({cout, y} == ({1'b0, a} + {1'b0, b}))
    );

    // SUB returns the 8-bit difference and borrow flag.
    check_sub_result: assert property (
        @(posedge clk)
        (op == ALUOP_SUB) |-> ((y == (a - b)) && (cout == (a < b)))
    );

    // AND returns a & b and clears carry-out.
    check_and_result: assert property (
        @(posedge clk)
        (op == ALUOP_AND) |-> ((y == (a & b)) && (cout == 1'b0))
    );

    // OR returns a | b and clears carry-out.
    check_or_result: assert property (
        @(posedge clk)
        (op == ALUOP_OR) |-> ((y == (a | b)) && (cout == 1'b0))
    );

    // XOR returns a ^ b and clears carry-out.
    check_xor_result: assert property (
        @(posedge clk)
        (op == ALUOP_XOR) |-> ((y == (a ^ b)) && (cout == 1'b0))
    );

    // COM returns bitwise complement of a and clears carry-out.
    check_com_result: assert property (
        @(posedge clk)
        (op == ALUOP_COM) |-> ((y == (~a)) && (cout == 1'b0))
    );

    // ROR rotates right through cin and shifts out a[0] to carry-out.
    check_ror_result: assert property (
        @(posedge clk)
        (op == ALUOP_ROR) |-> ((y == {cin, a[7:1]}) && (cout == a[0]))
    );

    // ROL rotates left through cin and shifts out a[7] to carry-out.
    check_rol_result: assert property (
        @(posedge clk)
        (op == ALUOP_ROL) |-> ((y == {a[6:0], cin}) && (cout == a[7]))
    );

    // SWAP exchanges nibbles of a and clears carry-out.
    check_swap_result: assert property (
        @(posedge clk)
        (op == ALUOP_SWAP) |-> ((y == {a[3:0], a[7:4]}) && (cout == 1'b0))
    );

    // Undefined operations drive zero result and clear carry-out.
    check_default_result: assert property (
        @(posedge clk)
        (op != ALUOP_ADD  &&
         op != ALUOP_SUB  &&
         op != ALUOP_AND  &&
         op != ALUOP_OR   &&
         op != ALUOP_XOR  &&
         op != ALUOP_COM  &&
         op != ALUOP_ROR  &&
         op != ALUOP_ROL  &&
         op != ALUOP_SWAP) |-> ((y == 8'h00) && (cout == 1'b0))
    );

    // zout always reflects whether y is zero.
    check_zero_flag: assert property (
        @(posedge clk)
        (zout == (y == 8'h00))
    );

endmodule