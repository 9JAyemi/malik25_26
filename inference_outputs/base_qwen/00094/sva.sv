module RippleAdder2_sva (
    input wire clk,
    input wire rst_n,
    input wire [3:0] a,
    input wire [3:0] b,
    input wire ci,
    output reg co,
    output reg [3:0] s
);
    // FullAdder outputs
    wire [3:0] fa_0_s;
    wire fa_0_co;
    wire [3:0] fa_1_s;
    wire fa_1_co;
    wire [3:0] fa_2_s;
    wire fa_2_co;
    wire [3:0] fa_3_s;
    wire fa_3_co;

    // Internal signals
    reg [4:0] c;

    // FullAdder instances
    FullAdder fa_0_inst (
        .a(a[0]),
        .b(b[0]),
        .ci(ci),
        .co(fa_0_co),
        .s(fa_0_s)
    );

    FullAdder fa_1_inst (
        .a(a[1]),
        .b(b[1]),
        .ci(fa_0_co),
        .co(fa_1_co),
        .s(fa_1_s)
    );

    FullAdder fa_2_inst (
        .a(a[2]),
        .b(b[2]),
        .ci(fa_1_co),
        .co(fa_2_co),
        .s(fa_2_s)
    );

    FullAdder fa_3_inst (
        .a(a[3]),
        .b(b[3]),
        .ci(fa_2_co),
        .co(fa_3_co),
        .s(fa_3_s)
    );

    // Combinational logic for carry
    always @(ci, fa_0_co, fa_1_co, fa_2_co, fa_3_co) begin: assig_process_c
        c = {{{{fa_3_co, fa_2_co}, fa_1_co}, fa_0_co}, ci};
    end

    // Combinational logic for carry out
    always @(c) begin: assig_process_co
        co = c[4];
    end

    // Combinational logic for sum
    always @(fa_0_s, fa_1_s, fa_2_s, fa_3_s) begin: assig_process_s
        s = {{{fa_3_s, fa_2_s}, fa_1_s}, fa_0_s};
    end

    // Property: Carry out is correct
    carry_out_correct: assert property (
        @(posedge clk) disable iff (!rst_n) co == c[4]
    );

    // Property: Sum is correct
    sum_correct: assert property (
        @(posedge clk) disable iff (!rst_n) s == {{{fa_3_s, fa_2_s}, fa_1_s}, fa_0_s}
    );

    // Property: FullAdder 0 carry out is correct
    fa_0_co_correct: assert property (
        @(posedge clk) disable iff (!rst_n) fa_0_co == (a[0] & b[0] | (a[0] & ci) | (b[0] & ci))
    );

    // Property: FullAdder 0 sum is correct
    fa_0_s_correct: assert property (
        @(posedge clk) disable iff (!rst_n) fa_0_s == (a[0] ^ b[0] ^ ci)
    );

    // Property: FullAdder 1 carry out is correct
    fa_1_co_correct: assert property (
        @(posedge clk) disable iff (!rst_n) fa_1_co == (a[1] & b[1] | (a[1] & fa_0_co) | (b[1] & fa_0_co))
    );

    // Property: FullAdder 1 sum is correct
    fa_1_s_correct: assert property (
        @(posedge clk) disable iff (!rst_n) fa_1_s == (a[1] ^ b[1] ^ fa_0_co)
    );

    // Property: FullAdder 2 carry out is correct
    fa_2_co_correct: assert property (
        @(posedge clk) disable iff (!rst_n) fa_2_co == (a[2] & b[2] | (a[2] & fa_1_co) | (b[2] & fa_1_co))
    );

    // Property: FullAdder 2 sum is correct
    fa_2_s_correct: assert property (
        @(posedge clk) disable iff (!rst_n) fa_2_s == (a[2] ^ b[2] ^ fa_1_co)
    );

    // Property: FullAdder 3 carry out is correct
    fa_3_co_correct: assert property (
        @(posedge clk) disable iff (!rst_n) fa_3_co == (a[3] & b[3] | (a[3] & fa_2_co) | (b[3] & fa_2_co))
    );

    // Property: FullAdder 3 sum is correct
    fa_3_s_correct: assert property (
        @(posedge clk) disable iff (!rst_n) fa_3_s == (a[3] ^ b[3] ^ fa_2_co)
    );

    // Property: Reset drives outputs to zero
    reset_outputs_zero: assert property (
        @(posedge clk) !rst_n |-> (co == 1'b0) && (s == 4'b0000)
    );

endmodule