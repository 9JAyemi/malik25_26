module sha2_sec_ti2_rm0_ti2_and_l0_sva #(
    parameter NOTA = 1'b0,
    parameter NOTB = 1'b0,
    parameter NOTY = 1'b0
) (
    input wire clk,
    input wire [1:0] i_a,
    input wire [1:0] i_b,
    input wire [1:0] o_y
);

    wire [1:0] a;
    wire [1:0] b;
    wire n00, n10, n01, n11;

    assign a = i_a ^ {2{NOTA[0]}};
    assign b = i_b ^ {2{NOTB[0]}};

    assign n00 = ~(a[0] & b[0]);
    assign n10 = ~(a[1] & b[0]);
    assign n01 = ~(a[0] & b[1]);
    assign n11 = ~(a[1] & b[1]);

    // o_y[0] matches the RTL XOR of the two NAND terms and NOTY.
    check_output0_nand_equation: assert property (
        @(posedge clk) o_y[0] == (n00 ^ n11 ^ NOTY[0])
    );

    // o_y[1] matches the RTL XOR of the two cross-share NAND terms.
    check_output1_nand_equation: assert property (
        @(posedge clk) o_y[1] == (n10 ^ n01)
    );

    // The full output bus matches the equivalent simplified AND/XOR form.
    check_output_bus_simplified_equation: assert property (
        @(posedge clk) o_y == {
            ((a[1] & b[0]) ^ (a[0] & b[1])),
            ((a[0] & b[0]) ^ (a[1] & b[1]) ^ NOTY[0])
        }
    );

endmodule