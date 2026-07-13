module top_module_sva (
    input logic CLK,
    input logic [1:0] A,
    input logic [1:0] B,
    input logic [2:0] out
);
    // out MSB is always 0 (result range is 0..3).
    check_out_msb_zero: assert property (
        @(posedge CLK) out[2] == 1'b0
    );

    // Lower two bits equal (A - B) modulo 4.
    check_out_lowerbits_moddiff: assert property (
        @(posedge CLK) out[1:0] == (A - B)
    );

    // When A == B, output is zero.
    check_equal_inputs_zero_out: assert property (
        @(posedge CLK) (A == B) |-> (out == 3'b000)
    );

    // When A > B, output is the non-wrapped difference.
    check_greater_no_wrap: assert property (
        @(posedge CLK) (A > B) |-> (out == {1'b0, (A - B)})
    );

    // When A < B, wrapped result is non-zero.
    check_less_wrap_nonzero: assert property (
        @(posedge CLK) (A < B) |-> (out[1:0] != 2'b00)
    );

    // When B == 0, output passes through A.
    check_B_zero_passthrough_A: assert property (
        @(posedge CLK) (B == 2'b00) |-> (out == {1'b0, A})
    );

    // When A == 0, output equals (0 - B) modulo 4.
    check_A_zero_wrap_from_B: assert property (
        @(posedge CLK) (A == 2'b00) |-> (out == {1'b0, (2'b00 - B)})
    );

    // When A == 3, output equals (3 - B) modulo 4.
    check_A_max_minus_B: assert property (
        @(posedge CLK) (A == 2'b11) |-> (out == {1'b0, (2'b11 - B)})
    );

    // If inputs are stable cycle-to-cycle, output is stable.
    check_stable_inputs_imply_stable_out: assert property (
        @(posedge CLK) $stable(A) && $stable(B) |-> $stable(out)
    );
endmodule