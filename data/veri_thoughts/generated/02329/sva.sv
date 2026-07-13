module full_adder_generic_sva #(
    parameter int WIDTH = 2
) (
    input  logic                    CLK,
    input  logic [WIDTH-1:0]        Ain,
    input  logic [WIDTH-1:0]        Bin,
    input  logic                    Cin,
    input  logic [WIDTH-1:0]        Sum,
    input  logic                    Cout
);
    // Sum and carry must equal the numeric addition of inputs
    check_concat_add: assert property (
        @(posedge CLK) {Cout, Sum} == (Ain + Bin + Cin)
    );

    // Sum equals low WIDTH bits of the numeric addition
    check_sum_modulo: assert property (
        @(posedge CLK) Sum == (Ain + Bin + Cin)[WIDTH-1:0]
    );

    // Cout equals the carry bit of the WIDTH+1-bit addition
    check_cout_bit: assert property (
        @(posedge CLK) Cout == ({1'b0, Ain} + {1'b0, Bin} + Cin)[WIDTH]
    );

    // LSB sum equals XOR of LSB inputs and Cin
    check_lsb_xor: assert property (
        @(posedge CLK) Sum[0] == (Ain[0] ^ Bin[0] ^ Cin)
    );

    // 0 + 0 + 0 yields Sum=0 and Cout=0
    check_zero_plus_zero_nocin: assert property (
        @(posedge CLK) (Ain == {WIDTH{1'b0}}) && (Bin == {WIDTH{1'b0}}) && (Cin == 1'b0)
            |-> (Sum == {WIDTH{1'b0}}) && (Cout == 1'b0)
    );

    // 0 + 0 + 1 yields Sum=1 at LSB and Cout=0
    check_zero_plus_zero_cin: assert property (
        @(posedge CLK) (Ain == {WIDTH{1'b0}}) && (Bin == {WIDTH{1'b0}}) && (Cin == 1'b1)
            |-> (Sum == {{(WIDTH-1){1'b0}}, 1'b1}) && (Cout == 1'b0)
    );

    // A + 0 + 0 yields Sum=A and Cout=0
    check_bzero_cin0: assert property (
        @(posedge CLK) (Bin == {WIDTH{1'b0}}) && (Cin == 1'b0)
            |-> (Sum == Ain) && (Cout == 1'b0)
    );

    // 0 + B + 0 yields Sum=B and Cout=0
    check_azero_cin0: assert property (
        @(posedge CLK) (Ain == {WIDTH{1'b0}}) && (Cin == 1'b0)
            |-> (Sum == Bin) && (Cout == 1'b0)
    );

    // MAX + 0 + 1 yields Sum=0 and Cout=1
    check_max_plus_one_a: assert property (
        @(posedge CLK) (Ain == {WIDTH{1'b1}}) && (Bin == {WIDTH{1'b0}}) && (Cin == 1'b1)
            |-> (Sum == {WIDTH{1'b0}}) && (Cout == 1'b1)
    );

    // 0 + MAX + 1 yields Sum=0 and Cout=1
    check_max_plus_one_b: assert property (
        @(posedge CLK) (Bin == {WIDTH{1'b1}}) && (Ain == {WIDTH{1'b0}}) && (Cin == 1'b1)
            |-> (Sum == {WIDTH{1'b0}}) && (Cout == 1'b1)
    );

    // MAX + MAX + 1 yields Sum=MAX and Cout=1
    check_max_plus_max_plus_one: assert property (
        @(posedge CLK) (Ain == {WIDTH{1'b1}}) && (Bin == {WIDTH{1'b1}}) && (Cin == 1'b1)
            |-> (Sum == {WIDTH{1'b1}}) && (Cout == 1'b1)
    );

    // With Cin=0, Cout equals carry bit of Ain+Bin
    check_cout_when_cin0: assert property (
        @(posedge CLK) (Cin == 1'b0)
            |-> (Cout == ({1'b0, Ain} + {1'b0, Bin})[WIDTH])
    );
endmodule