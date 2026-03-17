module adder_4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic Clk,
    input logic [3:0] S,
    input logic Cout
);

    // Registered outputs equal the previous cycle's 5-bit addition.
    check_registered_sum: assert property (
        @(posedge Clk)
        !$initstate |-> ({Cout, S} == ({1'b0, $past(A)} + {1'b0, $past(B)} + {4'b0, $past(Cin)}))
    );

    // Sum output is the low 4 bits of the previous cycle's addition.
    check_sum_low_bits: assert property (
        @(posedge Clk)
        !$initstate |-> (S == ($past(A) + $past(B) + $past(Cin)))
    );

    // Carry-out reflects overflow of the previous cycle's addition.
    check_carry_out_matches_overflow: assert property (
        @(posedge Clk)
        !$initstate |-> (Cout == (({1'b0, $past(A)} + {1'b0, $past(B)} + {4'b0, $past(Cin)}) >= 5'd16))
    );

    // With previous Cin low, the registered result is A plus B.
    check_cin_low_branch: assert property (
        @(posedge Clk)
        !$initstate && !$past(Cin) |-> ({Cout, S} == ({1'b0, $past(A)} + {1'b0, $past(B)}))
    );

    // With previous Cin high, the registered result is A plus B plus 1.
    check_cin_high_branch: assert property (
        @(posedge Clk)
        !$initstate && $past(Cin) |-> ({Cout, S} == ({1'b0, $past(A)} + {1'b0, $past(B)} + 5'd1))
    );

endmodule