module adder_32bit_sva (
    input logic        clk,
    input logic [31:0] A,
    input logic [31:0] B,
    input logic        Cin,
    input logic [31:0] Sum,
    input logic        Cout,
    input logic [31:0] carry,
    input logic [31:0] sum
);

    // Bit 0 sum follows the first full-adder XOR logic.
    check_bit0_sum_logic: assert property (
        @(posedge clk)
        sum[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Bit 0 carry follows the first full-adder carry logic.
    check_bit0_carry_logic: assert property (
        @(posedge clk)
        carry[0] == ((A[0] & B[0]) | (Cin & (A[0] ^ B[0])))
    );

    genvar i;
    generate
        for (i = 1; i < 31; i = i + 1) begin : gen_full_adder_chain_checks
            // Each intermediate sum bit follows full-adder XOR logic.
            check_sum_bit_logic: assert property (
                @(posedge clk)
                sum[i] == (A[i] ^ B[i] ^ carry[i-1])
            );

            // Each intermediate carry bit follows full-adder carry logic.
            check_carry_bit_logic: assert property (
                @(posedge clk)
                carry[i] == ((A[i] & B[i]) | (carry[i-1] & (A[i] ^ B[i])))
            );
        end
    endgenerate

    // Lower output bits are driven from the intermediate sum bus.
    check_lower_sum_output_mapping: assert property (
        @(posedge clk)
        Sum[30:0] == sum[30:0]
    );

    // The MSB sum follows the final full-adder XOR logic.
    check_msb_sum_logic: assert property (
        @(posedge clk)
        Sum[31] == (A[31] ^ B[31] ^ carry[30])
    );

    // Carry-out follows the final full-adder carry logic.
    check_cout_logic: assert property (
        @(posedge clk)
        Cout == ((A[31] & B[31]) | (carry[30] & (A[31] ^ B[31])))
    );

endmodule