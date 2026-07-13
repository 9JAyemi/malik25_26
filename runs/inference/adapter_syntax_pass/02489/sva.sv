module ripple_adder_32_sva (
    input logic CLK,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic cin,
    input logic [31:0] sum,
    input logic cout
);
    // Sum and carry-out equal 32-bit addition of a, b, and cin.
    check_total_sum: assert property (
        @(posedge CLK) {cout, sum} == ({1'b0, a} + {1'b0, b} + {31'b0, cin})
    );

    // LSB sum equals XOR of a[0], b[0], and cin.
    check_lsb_sum: assert property (
        @(posedge CLK) sum[0] == (a[0] ^ b[0] ^ cin)
    );

    // Carry-out equals majority of a[0], b[0], and cin.
    check_cout_majority: assert property (
        @(posedge CLK) cout == ((a[0] & b[0]) | (a[0] & cin) | (b[0] & cin))
    );

    // If b is zero and cin is zero, sum equals a and carry-out is zero.
    check_b_zero_cin_zero: assert property (
        @(posedge CLK) (b == 32'h00000000 && cin == 1'b0) |-> (sum == a && cout == 1'b0)
    );

    // If a is zero and cin is zero, sum equals b and carry-out is zero.
    check_a_zero_cin_zero: assert property (
        @(posedge CLK) (a == 32'h00000000 && cin == 1'b0) |-> (sum == b && cout == 1'b0)
    );

    // If a and b are zero, sum equals cin and carry-out is zero.
    check_ab_zero: assert property (
        @(posedge CLK) (a == 32'h00000000 && b == 32'h00000000) |-> (sum == {31'b0, cin} && cout == 1'b0)
    );

    // If a and b are all ones, sum equals all ones and carry-out is one.
    check_ab_all_ones: assert property (
        @(posedge CLK) (a == 32'hFFFFFFFF && b == 32'hFFFFFFFF) |-> (sum == 32'hFFFFFFFF && cout == 1'b1)
    );

    // If a is all ones and b is zero, sum equals all ones and carry-out is one.
    check_a_all_ones_b_zero: assert property (
        @(posedge CLK) (a == 32'hFFFFFFFF && b == 32'h00000000) |-> (sum == 32'hFFFFFFFF && cout == 1'b1)
    );

    // If a is zero and b is all ones, sum equals all ones and carry-out is one.
    check_a_zero_b_all_ones: assert property (
        @(posedge CLK) (a == 32'h00000000 && b == 32'hFFFFFFFF) |-> (sum == 32'hFFFFFFFF && cout == 1'b1)
    );

    // If a and b are all zeros, sum equals cin and carry-out is zero.
    check_ab_zero_cin: assert property (
        @(posedge CLK) (a == 32'h00000000 && b == 32'h00000000) |-> (sum == {31'b0, cin} && cout == 1'b0)
    );
endmodule