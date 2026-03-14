module Sumador_sva (
    input logic CLK,               // Sampling clock for assertions (DUT is combinational; no reset)
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [31:0] Z,
    input logic ovf
);

    // 32-bit zero-extended sum of 31-bit magnitudes
    function automatic [31:0] sum31(input logic [30:0] x, input logic [30:0] y);
        sum31 = {1'b0, x} + {1'b0, y};
    endfunction

    // 31-bit absolute difference of magnitudes
    function automatic [30:0] absdiff31(input logic [30:0] x, input logic [30:0] y);
        absdiff31 = (x >= y) ? (x - y) : (y - x);
    endfunction

    ///// Equal-sign path /////
    // When signs match, {ovf,Z[30:0]} equals zero-extended sum of magnitudes.
    check_eqsign_sum: assert property (
        @(posedge CLK) disable iff (1'b0) (a[31] == b[31]) |-> ({ovf, Z[30:0]} == sum31(a[30:0], b[30:0]))
    );

    // When signs match, Z's sign equals the inputs' sign.
    check_eqsign_signbit: assert property (
        @(posedge CLK) disable iff (1'b0) (a[31] == b[31]) |-> (Z[31] == a[31])
    );

    // When signs match and one magnitude is zero, output passes through the other with no overflow.
    check_eqsign_b_zero_passthru: assert property (
        @(posedge CLK) disable iff (1'b0) (a[31] == b[31] && (b[30:0] == 31'd0)) |-> (Z[30:0] == a[30:0] && Z[31] == a[31] && ovf == 1'b0)
    );

    // Symmetric passthrough when a's magnitude is zero.
    check_eqsign_a_zero_passthru: assert property (
        @(posedge CLK) disable iff (1'b0) (a[31] == b[31] && (a[30:0] == 31'd0)) |-> (Z[30:0] == b[30:0] && Z[31] == b[31] && ovf == 1'b0)
    );

    ///// Different-sign path /////
    // When signs differ, overflow is always zero.
    check_diffsign_ovf_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (a[31] != b[31]) |-> (ovf == 1'b0)
    );

    // When signs differ, Z's magnitude is the absolute difference of magnitudes.
    check_diffsign_absdiff: assert property (
        @(posedge CLK) disable iff (1'b0) (a[31] != b[31]) |-> (Z[30:0] == absdiff31(a[30:0], b[30:0]))
    );

    // When signs differ and magnitudes are equal, result is exactly zero.
    check_diffsign_equal_mags_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (a[31] != b[31] && a[30:0] == b[30:0]) |-> (Z == 32'd0)
    );

    // When signs differ and |a| > |b|, Z's sign equals a's sign.
    check_diffsign_sign_from_a: assert property (
        @(posedge CLK) disable iff (1'b0) (a[31] != b[31] && a[30:0] > b[30:0]) |-> (Z[31] == a[31])
    );

    // When signs differ and |b| > |a|, Z's sign equals b's sign.
    check_diffsign_sign_from_b: assert property (
        @(posedge CLK) disable iff (1'b0) (a[31] != b[31] && b[30:0] > a[30:0]) |-> (Z[31] == b[31])
    );

    ///// General consistency /////
    // ovf can only be high when input signs match.
    check_ovf_only_on_eqsign: assert property (
        @(posedge CLK) disable iff (1'b0) ovf |-> (a[31] == b[31])
    );

    // Pure combinational behavior: if inputs are stable, outputs remain stable.
    check_pure_comb: assert property (
        @(posedge CLK) disable iff (1'b0) ($stable(a) && $stable(b)) |-> ($stable(Z) && $stable(ovf))
    );

endmodule