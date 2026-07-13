module booth_multiplier_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [7:0] Y
);
    // Helper: exact RTL-computed Y for given A,B.
    function automatic logic [7:0] expected_Y (input logic [3:0] x, input logic [3:0] y);
        logic [7:0] p;
        logic [4:0] s;
        begin
            p = ({4'b0, x} * {4'b0, y})[7:0];
            s = {p[7], p[6:4]} + ({1'b0, p[3:1]} ^ {1'b0, p[2:0]});
            expected_Y = {s[4], s[3:0], p[3:0]};
        end
    endfunction

    ///// Functional correctness w.r.t. RTL expression /////
    // Y exactly matches the RTL-specified function of A and B.
    check_full_output_matches_spec: assert property (
        @(posedge CLK) disable iff (1'b0) Y == expected_Y(A, B)
    );

    // Low nibble of Y equals low nibble of product.
    check_low_nibble_product: assert property (
        @(posedge CLK) disable iff (1'b0) Y[3:0] == (({4'b0, A} * {4'b0, B})[3:0])
    );

    // Middle nibble of Y matches the RTL sum/xor construction from product bits.
    check_mid_nibble_spec: assert property (
        @(posedge CLK) disable iff (1'b0)
            Y[6:3] == (
                {(({4'b0, A} * {4'b0, B})[7]), ({4'b0, A} * {4'b0, B})[6:4]} +
                ({1'b0, ({4'b0, A} * {4'b0, B})[3:1]} ^ {1'b0, ({4'b0, A} * {4'b0, B})[2:0]})
            )[3:0]
    );

    // MSB of Y is always zero due to width truncation then zero-extension in S assignment.
    check_msb_zero: assert property (
        @(posedge CLK) disable iff (1'b0) Y[7] == 1'b0
    );

    ///// Basic invariants implied by the combinational RTL /////
    // If inputs are stable across a cycle, output is stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (1'b0) ($stable(A) && $stable(B)) |-> $stable(Y)
    );

    // If either operand is zero, output Y is zero.
    check_zero_operand_outputs_zero: assert property (
        @(posedge CLK) disable iff (1'b0) ((A == 4'd0) || (B == 4'd0)) |-> (Y == 8'd0)
    );

    // Swapping A and B across consecutive cycles does not change Y (commutativity).
    check_commutative_swap: assert property (
        @(posedge CLK) disable iff (1'b0) (A == $past(B) && B == $past(A)) |-> (Y == $past(Y))
    );

    // LSB of Y equals AND of operand LSBs (LSB of product).
    check_lsb_and: assert property (
        @(posedge CLK) disable iff (1'b0) Y[0] == (A[0] & B[0])
    );
endmodule