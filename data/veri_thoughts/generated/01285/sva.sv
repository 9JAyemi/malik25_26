module bitwise_op_sva (
    // Environment clock for sampling; DUT has no clock/reset (pure combinational)
    input logic clk,
    // DUT ports
    input logic [31:0] x,
    input logic [31:0] y,
    input logic [31:0] z,
    input logic [31:0] o
);
    // o matches the RTL expression exactly.
    check_output_matches_rtl_expr: assert property (
        @(posedge clk) o == (z ^ (x & (y ^ z)))
    );

    // o is equivalent to a bitwise mux: x ? y : z.
    check_mux_equivalence: assert property (
        @(posedge clk) o == ((x & y) | (~x & z))
    );

    // The XOR of o and z equals x masked with (y^z).
    check_xor_mask_relation: assert property (
        @(posedge clk) (o ^ z) == (x & (y ^ z))
    );

    // When x is all zeros, o must pass through z.
    check_pass_through_when_x_zero: assert property (
        @(posedge clk) (x == 32'b0) |-> (o == z)
    );

    // When x is all ones, o must equal y.
    check_select_y_when_x_all_ones: assert property (
        @(posedge clk) (x == 32'hFFFF_FFFF) |-> (o == y)
    );

    // When y equals z, o must equal z.
    check_when_y_equals_z: assert property (
        @(posedge clk) (y == z) |-> (o == z)
    );

    // When z is all zeros, o reduces to x & y.
    check_when_z_zero: assert property (
        @(posedge clk) (z == 32'b0) |-> (o == (x & y))
    );

    // When y is all zeros, o reduces to (~x) & z.
    check_when_y_zero: assert property (
        @(posedge clk) (y == 32'b0) |-> (o == ((~x) & z))
    );

    // Bits selected by x must match y (masked equality).
    check_y_path_mask: assert property (
        @(posedge clk) (o & x) == (y & x)
    );

    // Bits not selected by x must match z (masked equality).
    check_z_path_mask: assert property (
        @(posedge clk) (o & ~x) == (z & ~x)
    );
endmodule