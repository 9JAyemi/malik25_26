module four_bit_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic Clock,
    input logic [3:0] Sum,
    input logic Cout
);
    // Clock: Clock (posedge). Reset: none. Logic: sequential 1-cycle add with carry-out.

    // Sum equals the 4-bit addition of A, B, and Cin from the previous cycle.
    check_sum_matches_prev_cycle_add: assert property (
        @(posedge Clock) disable iff ($initstate) Sum == $past(A + B + Cin)[3:0]
    );

    // Cout equals the carry-out of the 4-bit addition from the previous cycle.
    check_cout_matches_prev_cycle_carry: assert property (
        @(posedge Clock) disable iff ($initstate) Cout == $past(A + B + Cin)[4]
    );

    // If A, B, and Cin are unchanged from the previous cycle, Sum and Cout repeat.
    check_outputs_repeat_when_inputs_repeat: assert property (
        @(posedge Clock) disable iff ($initstate) (A == $past(A) && B == $past(B) && Cin == $past(Cin)) |-> (Sum == $past(Sum) && Cout == $past(Cout))
    );

    // With B=0 and Cin=0, Sum equals A from the previous cycle.
    check_sum_when_B_zero_and_Cin_zero: assert property (
        @(posedge Clock) disable iff ($initstate) (B == 4'b0000 && Cin == 1'b0) |-> (Sum == $past(A)[3:0])
    );

    // With A=0 and Cin=0, Sum equals B from the previous cycle.
    check_sum_when_A_zero_and_Cin_zero: assert property (
        @(posedge Clock) disable iff ($initstate) (A == 4'b0000 && Cin == 1'b0) |-> (Sum == $past(B)[3:0])
    );

    // With A=0 and B=0, Sum equals Cin from the previous cycle.
    check_sum_when_A_zero_and_B_zero: assert property (
        @(posedge Clock) disable iff ($initstate) (A == 4'b0000 && B == 4'b0000) |-> (Sum == $past(Cin))
    );

    // With A=0 and B=0, Cout is 0 from the previous cycle.
    check_cout_when_A_zero_and_B_zero: assert property (
        @(posedge Clock) disable iff ($initstate) (A == 4'b0000 && B == 4'b0000) |-> (Cout == 1'b0)
    );

    // With A=0 and Cin=0, Cout equals MSB of B from the previous cycle.
    check_cout_when_A_zero_and_Cin_zero: assert property (
        @(posedge Clock) disable iff ($initstate) (A == 4'b0000 && Cin == 1'b0) |-> (Cout == $past(B[3]))
    );

    // With B=0 and Cin=0, Cout equals MSB of A from the previous cycle.
    check_cout_when_B_zero_and_Cin_zero: assert property (
        @(posedge Clock) disable iff ($initstate) (B == 4'b0000 && Cin == 1'b0) |-> (Cout == $past(A[3]))
    );

    // With A=0 and B=0, Cout equals Cin from the previous cycle.
    check_cout_when_A_zero_and_B_zero: assert property (
        @(posedge Clock) disable iff ($initstate) (A == 4'b0000 && B == 4'b0000) |-> (Cout == $past(Cin))
    );

    // With A=0 and B=0, Cout equals Cin from the previous cycle.
    check_cout_when_A_zero_and_B_zero: assert property (
        @(posedge Clock) disable iff ($initstate) (A == 4'b0000 && B == 4'b0000) |-> (Cout == $past(Cin))
    );

    // With A=0 and B=0, Cout equals Cin from the previous cycle.
    check_cout_when_A_zero_and_B_zero: assert property (
        @(posedge Clock) disable iff ($initstate) (A == 4'b0000 && B == 4'b0000) |-> (Cout == $past(Cin))
    );

endmodule