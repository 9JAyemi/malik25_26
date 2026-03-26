module adder_4bit_sva (
    input logic clk,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic cin,
    input logic [3:0] out,
    input logic cout,
    input logic [3:0] sum,
    input logic c1,
    input logic c2,
    input logic c3
);

    // The top-level output is the internal sum bus.
    check_out_matches_sum: assert property (
        @(posedge clk) out == sum
    );

    // Bit 0 sum matches the full-adder XOR equation.
    check_stage0_sum: assert property (
        @(posedge clk) sum[0] == (in1[0] ^ in2[0] ^ cin)
    );

    // Stage 0 carry matches the full-adder carry equation.
    check_stage0_carry: assert property (
        @(posedge clk) c1 == ((in1[0] & in2[0]) | ((in1[0] ^ in2[0]) & cin))
    );

    // Bit 1 sum uses the ripple carry from stage 0.
    check_stage1_sum: assert property (
        @(posedge clk) sum[1] == (in1[1] ^ in2[1] ^ c1)
    );

    // Stage 1 carry matches the full-adder carry equation.
    check_stage1_carry: assert property (
        @(posedge clk) c2 == ((in1[1] & in2[1]) | ((in1[1] ^ in2[1]) & c1))
    );

    // Bit 2 sum uses the ripple carry from stage 1.
    check_stage2_sum: assert property (
        @(posedge clk) sum[2] == (in1[2] ^ in2[2] ^ c2)
    );

    // Stage 2 carry matches the full-adder carry equation.
    check_stage2_carry: assert property (
        @(posedge clk) c3 == ((in1[2] & in2[2]) | ((in1[2] ^ in2[2]) & c2))
    );

    // Bit 3 sum uses the ripple carry from stage 2.
    check_stage3_sum: assert property (
        @(posedge clk) sum[3] == (in1[3] ^ in2[3] ^ c3)
    );

    // Final carry-out matches the full-adder carry equation.
    check_stage3_carry: assert property (
        @(posedge clk) cout == ((in1[3] & in2[3]) | ((in1[3] ^ in2[3]) & c3))
    );

    // The full 5-bit result matches arithmetic addition.
    check_full_sum: assert property (
        @(posedge clk) {cout, out} == ({1'b0, in1} + {1'b0, in2} + cin)
    );

endmodule