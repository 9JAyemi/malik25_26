module full_adder_sva (
    input logic A,
    input logic B,
    input logic C_in,
    input logic Sum,
    input logic C_out
);

    // Sum equals A^B^C_in on A rising edge.
    check_sum_func_on_A: assert property (
        @(posedge A) Sum == (A ^ B ^ C_in)
    );

    // Sum equals A^B^C_in on B rising edge.
    check_sum_func_on_B: assert property (
        @(posedge B) Sum == (A ^ B ^ C_in)
    );

    // Sum equals A^B^C_in on C_in rising edge.
    check_sum_func_on_Cin: assert property (
        @(posedge C_in) Sum == (A ^ B ^ C_in)
    );

    // C_out equals (A & B) | (C_in & (A ^ B)) on A rising edge.
    check_cout_func_on_A: assert property (
        @(posedge A) C_out == ((A & B) | (C_in & (A ^ B)))
    );

    // C_out equals (A & B) | (C_in & (A ^ B)) on B rising edge.
    check_cout_func_on_B: assert property (
        @(posedge B) C_out == ((A & B) | (C_in & (A ^ B)))
    );

    // C_out equals (A & B) | (C_in & (A ^ B)) on C_in rising edge.
    check_cout_func_on_Cin: assert property (
        @(posedge C_in) C_out == ((A & B) | (C_in & (A ^ B)))
    );

    // {C_out,Sum} equals A+B+C_in on A rising edge.
    check_bin_sum_on_A: assert property (
        @(posedge A) {C_out, Sum} == ({1'b0, A} + {1'b0, B} + {1'b0, C_in})
    );

    // {C_out,Sum} equals A+B+C_in on B rising edge.
    check_bin_sum_on_B: assert property (
        @(posedge B) {C_out, Sum} == ({1'b0, A} + {1'b0, B} + {1'b0, C_in})
    );

    // {C_out,Sum} equals A+B+C_in on C_in rising edge.
    check_bin_sum_on_Cin: assert property (
        @(posedge C_in) {C_out, Sum} == ({1'b0, A} + {1'b0, B} + {1'b0, C_in})
    );

endmodule