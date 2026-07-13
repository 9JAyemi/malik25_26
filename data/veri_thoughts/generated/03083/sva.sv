module carry_select_adder_32bit_sva (
    input logic        clk,
    input logic [31:0] A,
    input logic [31:0] B,
    input logic [31:0] S,
    input logic        Cout
);

    function automatic logic calc_g0(input logic [31:0] a, input logic [31:0] b);
        logic g;
        integer i;
        begin
            g = a[31] & b[31];
            for (i = 30; i >= 0; i = i - 1) begin
                g = (a[i] & b[i]) | ((a[i] ^ b[i]) & g);
            end
            calc_g0 = g;
        end
    endfunction

    function automatic logic calc_sum_lsb(input logic [31:0] a, input logic [31:0] b);
        begin
            calc_sum_lsb = (a[0] ^ b[0]) ^ calc_g0(a, b);
        end
    endfunction

    function automatic logic [31:0] calc_sum(input logic [31:0] a, input logic [31:0] b);
        begin
            calc_sum = {31'b0, calc_sum_lsb(a, b)};
        end
    endfunction

    // Cout matches the RTL's G31 assignment.
    check_cout_matches_msb_generate: assert property (
        @(posedge clk) Cout == (A[31] & B[31])
    );

    // The upper 31 sum bits are always zero in this implementation.
    check_sum_upper_bits_zero: assert property (
        @(posedge clk) S[31:1] == 31'b0
    );

    // The sum LSB matches the recursive G chain rooted at bit 0.
    check_sum_lsb_matches_recursive_chain: assert property (
        @(posedge clk) S[0] == calc_sum_lsb(A, B)
    );

    // The full sum vector matches the RTL expression for S.
    check_full_sum_matches_rtl_equation: assert property (
        @(posedge clk) S == calc_sum(A, B)
    );

    // Zero inputs produce zero outputs.
    check_zero_inputs_drive_zero_outputs: assert property (
        @(posedge clk) ((A == 32'b0) && (B == 32'b0)) |-> ((S == 32'b0) && (Cout == 1'b0))
    );

    // With all upper bits zero, the result reduces to the LSB OR and no carry-out.
    check_upper_zero_case_reduces_to_lsb_or: assert property (
        @(posedge clk) ((A[31:1] == 31'b0) && (B[31:1] == 31'b0)) |-> ((S == {31'b0, (A[0] | B[0])}) && (Cout == 1'b0))
    );

    // Equal low bits of 0 force the sum LSB low.
    check_lsb_zero_pair_drives_zero: assert property (
        @(posedge clk) ((A[0] == 1'b0) && (B[0] == 1'b0)) |-> (S[0] == 1'b0)
    );

    // Equal low bits of 1 force the sum LSB high.
    check_lsb_one_pair_drives_one: assert property (
        @(posedge clk) ((A[0] == 1'b1) && (B[0] == 1'b1)) |-> (S[0] == 1'b1)
    );

    // A high MSB pair forces carry-out high.
    check_msb_pair_high_forces_cout: assert property (
        @(posedge clk) ((A[31] == 1'b1) && (B[31] == 1'b1)) |-> (Cout == 1'b1)
    );

    // If the MSB pair is not both high, carry-out stays low.
    check_msb_pair_not_both_high_forces_no_cout: assert property (
        @(posedge clk) ((A[31] == 1'b0) || (B[31] == 1'b0)) |-> (Cout == 1'b0)
    );

endmodule