module decoderparam_sva
#(parameter int WIDTH = 4)
(
    input logic clk,
    input logic [(1<<WIDTH)-1:0] code,
    input logic [WIDTH-1:0] a,
    input logic clken
);

    localparam int OUTW = (1 << WIDTH);
    localparam logic [OUTW-1:0] DECODE_BASE = {{(OUTW-1){1'b0}}, 1'b1};
    localparam logic [OUTW-1:0] ZERO_VEC    = '0;

    // Output must equal the enabled one-hot decode of the address.
    check_code_matches_decode: assert property (
        @(posedge clk) code == (clken ? (DECODE_BASE << a) : ZERO_VEC)
    );

    // When disabled, all output bits must be low.
    check_disable_clears_code: assert property (
        @(posedge clk) !clken |-> (code == ZERO_VEC)
    );

    // The output must always be either all-zero or one-hot.
    check_code_is_onehot0: assert property (
        @(posedge clk) $onehot0(code)
    );

    genvar gi;
    generate
        for (gi = 0; gi < OUTW; gi = gi + 1) begin : gen_output_checks
            // Any asserted output bit must match the address and enable.
            check_output_bit_implies_address: assert property (
                @(posedge clk) code[gi] |-> (clken && (a == gi))
            );
        end
    endgenerate

endmodule