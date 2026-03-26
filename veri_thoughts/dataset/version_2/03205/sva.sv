module sky130_fd_sc_lp__fah_sva (
    input logic clk,
    input logic COUT,
    input logic SUM,
    input logic A,
    input logic B,
    input logic CI
);

    // No DUT clock or reset; sample this combinational logic on clk.

    // SUM must equal the 3-input XOR of A, B, and CI.
    check_sum_function: assert property (
        @(posedge clk) SUM == (A ^ B ^ CI)
    );

    // COUT must equal the majority/carry function of A, B, and CI.
    check_cout_function: assert property (
        @(posedge clk) COUT == ((A & B) | (A & CI) | (B & CI))
    );

    // All-zero inputs must produce zero SUM and zero COUT.
    check_zero_inputs: assert property (
        @(posedge clk) ({A, B, CI} == 3'b000) |-> ({COUT, SUM} == 2'b00)
    );

    // Any one-hot input pattern must produce SUM=1 and COUT=0.
    check_one_hot_inputs: assert property (
        @(posedge clk)
        (({A, B, CI} == 3'b001) ||
         ({A, B, CI} == 3'b010) ||
         ({A, B, CI} == 3'b100)) |-> ({COUT, SUM} == 2'b01)
    );

    // Any two-hot input pattern must produce SUM=0 and COUT=1.
    check_two_hot_inputs: assert property (
        @(posedge clk)
        (({A, B, CI} == 3'b011) ||
         ({A, B, CI} == 3'b101) ||
         ({A, B, CI} == 3'b110)) |-> ({COUT, SUM} == 2'b10)
    );

    // All-one inputs must produce SUM=1 and COUT=1.
    check_all_one_inputs: assert property (
        @(posedge clk) ({A, B, CI} == 3'b111) |-> ({COUT, SUM} == 2'b11)
    );

endmodule