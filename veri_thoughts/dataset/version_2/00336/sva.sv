module xor_module_sva #(
    parameter A_SIGNED = 0,
    parameter B_SIGNED = 0,
    parameter A_WIDTH  = 1,
    parameter B_WIDTH  = 1,
    parameter Y_WIDTH  = 1
) (
    input logic clk,
    input logic [A_WIDTH-1:0] A,
    input logic [B_WIDTH-1:0] B,
    input logic [Y_WIDTH-1:0] Y
);

    localparam int WIDTH = (A_WIDTH > B_WIDTH) ? A_WIDTH : B_WIDTH;
    localparam int LOWW  = (Y_WIDTH < WIDTH) ? Y_WIDTH : WIDTH;

    wire [WIDTH-1:0] a_ext;
    wire [WIDTH-1:0] b_ext;
    wire [WIDTH-1:0] xnor_val;

    assign a_ext    = A_SIGNED ? {{(WIDTH-A_WIDTH){A[A_WIDTH-1]}}, A} : A;
    assign b_ext    = B_SIGNED ? {{(WIDTH-B_WIDTH){B[B_WIDTH-1]}}, B} : B;
    assign xnor_val = ~(a_ext ^ b_ext);

    generate
        if (Y_WIDTH >= WIDTH) begin : gen_y_wide_enough
            // Entire output matches the zero-extended XNOR result.
            check_y_matches_xnor_wide: assert property (
                @(posedge clk) Y == {{(Y_WIDTH-WIDTH){1'b0}}, xnor_val}
            );
        end else begin : gen_y_truncated
            // Entire output matches the truncated XNOR result.
            check_y_matches_xnor_narrow: assert property (
                @(posedge clk) Y == xnor_val[Y_WIDTH-1:0]
            );
        end
    endgenerate

    generate
        if (Y_WIDTH > WIDTH) begin : gen_upper_bits
            // Output bits above the computed result width are zero.
            check_y_upper_bits_zero: assert property (
                @(posedge clk) Y[Y_WIDTH-1:WIDTH] == '0
            );
        end
    endgenerate

    // Stable inputs keep the combinational output stable.
    check_stable_inputs_keep_output_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> $stable(Y)
    );

    // A sampled output change requires a sampled input change.
    check_output_change_requires_input_change: assert property (
        @(posedge clk) $changed(Y) |-> ($changed(A) || $changed(B))
    );

    // Equal extended operands produce ones on implemented result bits.
    check_equal_operands_drive_ones: assert property (
        @(posedge clk) (a_ext == b_ext) |-> (Y[LOWW-1:0] == {LOWW{1'b1}})
    );

    // Complementary extended operands produce zeros on implemented result bits.
    check_complementary_operands_drive_zeros: assert property (
        @(posedge clk) (a_ext == ~b_ext) |-> (Y[LOWW-1:0] == {LOWW{1'b0}})
    );

endmodule