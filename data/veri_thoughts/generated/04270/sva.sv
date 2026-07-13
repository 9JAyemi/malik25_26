module four_bit_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CLK,
    input logic RST,
    input logic [4:0] SUM
);

    // Synchronous reset forces SUM to zero.
    check_reset_clears_sum: assert property (
        @(posedge CLK) RST |=> (SUM == 5'b00000)
    );

    // Outside reset, SUM reflects the prior cycle addition of A and B.
    check_sum_matches_previous_addition: assert property (
        @(posedge CLK) disable iff (RST)
        !RST |=> (SUM == ({1'b0, $past(A)} + {1'b0, $past(B)}))
    );

    // Zero operands produce a zero sum on the next sampled cycle.
    check_zero_inputs_produce_zero_sum: assert property (
        @(posedge CLK) disable iff (RST)
        (!RST && (A == 4'b0000) && (B == 4'b0000)) |=> (SUM == 5'b00000)
    );

    // Maximum operands produce 30 on the next sampled cycle.
    check_max_inputs_produce_thirty: assert property (
        @(posedge CLK) disable iff (RST)
        (!RST && (A == 4'b1111) && (B == 4'b1111)) |=> (SUM == 5'd30)
    );

    // When A is zero, SUM equals the prior cycle value of B.
    check_a_zero_passes_b: assert property (
        @(posedge CLK) disable iff (RST)
        (!RST && (A == 4'b0000)) |=> (SUM == {1'b0, $past(B)})
    );

    // When B is zero, SUM equals the prior cycle value of A.
    check_b_zero_passes_a: assert property (
        @(posedge CLK) disable iff (RST)
        (!RST && (B == 4'b0000)) |=> (SUM == {1'b0, $past(A)})
    );

endmodule