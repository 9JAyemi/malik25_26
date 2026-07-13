module ripple_carry_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic V
);

    // Registered outputs equal the previous cycle's 5-bit addition.
    check_registered_sum_and_carry: assert property (
        @(posedge clk)
        !$initstate |-> ({V, S} == ($past({1'b0, A}) + $past({1'b0, B}) + $past(Cin)))
    );

    // Bit 0 sum follows the first full-adder XOR equation from the previous cycle.
    check_lsb_sum_equation: assert property (
        @(posedge clk)
        !$initstate |-> (S[0] == ($past(A[0]) ^ $past(B[0]) ^ $past(Cin)))
    );

    // Carry-out matches whether the previous addition exceeded 4 bits.
    check_carry_out_threshold: assert property (
        @(posedge clk)
        !$initstate |-> (V == (($past({1'b0, A}) + $past({1'b0, B}) + $past(Cin)) >= 5'd16))
    );

    // Zero inputs with zero carry-in produce zero output on the next cycle.
    check_zero_addition_case: assert property (
        @(posedge clk)
        (!$initstate && ($past(A) == 4'b0000) && ($past(B) == 4'b0000) && ($past(Cin) == 1'b0))
        |-> ({V, S} == 5'b00000)
    );

    // All-ones inputs with carry-in produce all-ones output and carry-out on the next cycle.
    check_max_addition_case: assert property (
        @(posedge clk)
        (!$initstate && ($past(A) == 4'b1111) && ($past(B) == 4'b1111) && ($past(Cin) == 1'b1))
        |-> ({V, S} == 5'b11111)
    );

    // Repeating the same inputs across cycles keeps the registered output unchanged one cycle later.
    check_output_stable_when_inputs_repeat: assert property (
        @(posedge clk)
        (!$initstate && (A == $past(A)) && (B == $past(B)) && (Cin == $past(Cin)))
        |=> ({V, S} == $past({V, S}))
    );

endmodule