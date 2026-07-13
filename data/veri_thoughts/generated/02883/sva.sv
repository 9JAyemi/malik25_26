module salsa20_qr_sva (
    input logic [31:0] y0,
    input logic [31:0] y1,
    input logic [31:0] y2,
    input logic [31:0] y3,

    input logic [31:0] z0,
    input logic [31:0] z1,
    input logic [31:0] z2,
    input logic [31:0] z3
);
    // Helper rotate-left functions matching RTL structure.
    function automatic logic [31:0] rotl7 (input logic [31:0] v);
        rotl7 = {v[24:0], v[31:25]};
    endfunction
    function automatic logic [31:0] rotl9 (input logic [31:0] v);
        rotl9 = {v[22:0], v[31:23]};
    endfunction
    function automatic logic [31:0] rotl13 (input logic [31:0] v);
        rotl13 = {v[18:0], v[31:19]};
    endfunction
    function automatic logic [31:0] rotl18 (input logic [31:0] v);
        rotl18 = {v[13:0], v[31:14]};
    endfunction

    // Helper rotate-right functions for inverse checks.
    function automatic logic [31:0] rotr7 (input logic [31:0] v);
        rotr7 = {v[6:0], v[31:7]};
    endfunction
    function automatic logic [31:0] rotr9 (input logic [31:0] v);
        rotr9 = {v[8:0], v[31:9]};
    endfunction
    function automatic logic [31:0] rotr13 (input logic [31:0] v);
        rotr13 = {v[12:0], v[31:13]};
    endfunction
    function automatic logic [31:0] rotr18 (input logic [31:0] v);
        rotr18 = {v[17:0], v[31:18]};
    endfunction

    // z1 equals rotl7(y0 + y3) XOR y1.
    check_z1_def: assert property (
        @(posedge y0[0]) z1 == (rotl7(y0 + y3) ^ y1)
    );

    // z2 equals rotl9(z1 + y0) XOR y2.
    check_z2_def: assert property (
        @(posedge y0[0]) z2 == (rotl9(z1 + y0) ^ y2)
    );

    // z3 equals rotl13(z2 + z1) XOR y3.
    check_z3_def: assert property (
        @(posedge y0[0]) z3 == (rotl13(z2 + z1) ^ y3)
    );

    // z0 equals rotl18(z3 + z2) XOR y0.
    check_z0_def: assert property (
        @(posedge y0[0]) z0 == (rotl18(z3 + z2) ^ y0)
    );

    // Inverse of z1 relation using right rotate.
    check_z1_inverse: assert property (
        @(posedge y0[0]) rotr7(z1 ^ y1) == (y0 + y3)
    );

    // Inverse of z2 relation using right rotate.
    check_z2_inverse: assert property (
        @(posedge y0[0]) rotr9(z2 ^ y2) == (z1 + y0)
    );

    // Inverse of z3 relation using right rotate.
    check_z3_inverse: assert property (
        @(posedge y0[0]) rotr13(z3 ^ y3) == (z2 + z1)
    );

    // Inverse of z0 relation using right rotate.
    check_z0_inverse: assert property (
        @(posedge y0[0]) rotr18(z0 ^ y0) == (z3 + z2)
    );

    // If inputs are stable between samples, outputs are stable (combinational determinism).
    check_output_stability: assert property (
        @(posedge y0[0]) $stable({y0, y1, y2, y3}) |-> $stable({z0, z1, z2, z3})
    );
endmodule