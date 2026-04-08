module alu_sva (
    input logic [7:0] Aval,
    input logic [7:0] Bval,
    input logic       cin,
    input logic [1:0] op,
    input logic [7:0] ALUout,
    input logic       cout
);

    // op=00 selects addition with carry-in.
    check_add_mode_result: assert property (
        @($global_clock)
        (op == 2'b00) |-> ({cout, ALUout} == (Aval + Bval + cin))
    );

    // op=10 selects bitwise AND and forces carry low.
    check_and_mode_result: assert property (
        @($global_clock)
        (op == 2'b10) |-> ({cout, ALUout} == {1'b0, (Aval & Bval)})
    );

    // op=01 selects the XOR-modified 9-bit add result.
    check_xor_add_mode_result: assert property (
        @($global_clock)
        (op == 2'b01) |-> ({cout, ALUout} == (9'h100 ^ (Aval + Bval + 9'h001)))
    );

    // op=11 clears the output when the shift amount is greater than 7.
    check_shift_mode_large_amount_zero: assert property (
        @($global_clock)
        ((op == 2'b11) && (Bval > 7'h07)) |-> ({cout, ALUout} == 9'h000)
    );

    // op=11 shifts Aval left by Bval when the shift amount is 7 or less.
    check_shift_mode_small_amount_result: assert property (
        @($global_clock)
        ((op == 2'b11) && (Bval <= 7'h07)) |-> ({cout, ALUout} == {1'b0, (Aval << Bval)})
    );

endmodule