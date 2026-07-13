module four_bit_adder_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CIN,
    input logic [3:0] SUM,
    input logic COUT
);
    // Clock: CLK (posedge). No reset in RTL. Sequential registered adder.

    ///// Functional correctness /////
    // Next cycle output equals prior cycle 5-bit sum of inputs.
    check_registered_sum_full: assert property (
        @(posedge CLK) 1'b1 |=> {COUT, SUM} == $past({1'b0, A} + {1'b0, B} + CIN)
    );

    // Next cycle SUM equals low 4 bits of prior cycle addition.
    check_sum_low4: assert property (
        @(posedge CLK) 1'b1 |=> SUM == ($past({1'b0, A} + {1'b0, B} + CIN))[3:0]
    );

    // Next cycle COUT equals bit[4] (carry) of prior cycle addition.
    check_cout_bit4: assert property (
        @(posedge CLK) 1'b1 |=> COUT == ($past({1'b0, A} + {1'b0, B} + CIN))[4]
    );

    // Carry flag matches overflow (sum >= 16) from prior cycle inputs.
    check_cout_overflow_equiv: assert property (
        @(posedge CLK) 1'b1 |=> COUT == ($past({1'b0, A} + {1'b0, B} + CIN) >= 5'd16)
    );

    // All-zero inputs in prior cycle produce zero output next cycle.
    check_zero_case: assert property (
        @(posedge CLK) 1'b1 |=> (($past(A) == 4'd0) && ($past(B) == 4'd0) && ($past(CIN) == 1'b0)) |-> ({COUT, SUM} == 5'd0)
    );

    // Max-sum case (31) in prior cycle yields {COUT,SUM} == 5'b1_1111 next cycle.
    check_max_case: assert property (
        @(posedge CLK) 1'b1 |=> ($past({1'b0, A} + {1'b0, B} + CIN) == 5'd31) |-> ({COUT, SUM} == 5'b1_1111)
    );

endmodule