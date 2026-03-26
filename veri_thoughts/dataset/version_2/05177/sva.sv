module generic_baseblocks_v2_1_mux_sva #
(
    parameter         C_FAMILY     = "rtl",
    parameter integer C_SEL_WIDTH  = 4,
    parameter integer C_DATA_WIDTH = 2
)
(
    input logic                                     clk,
    input logic [C_SEL_WIDTH-1:0]                   S,
    input logic [(2**C_SEL_WIDTH)*C_DATA_WIDTH-1:0] A,
    input logic [C_DATA_WIDTH-1:0]                  O
);

    genvar sel_idx;
    generate
        for (sel_idx = 0; sel_idx < (2**C_SEL_WIDTH); sel_idx = sel_idx + 1) begin : gen_select_checks
            localparam integer SEL_LSB = sel_idx * C_DATA_WIDTH;
            localparam logic [C_SEL_WIDTH-1:0] SEL_VALUE = sel_idx;

            // O matches the slice of A selected by S.
            check_selected_slice: assert property (
                @(posedge clk) (S == SEL_VALUE) |-> (O == A[SEL_LSB +: C_DATA_WIDTH])
            );

            // O stays stable when S and the selected slice stay stable.
            check_output_stable_for_same_selection: assert property (
                @(posedge clk) ($stable(S) && (S == SEL_VALUE) && $stable(A[SEL_LSB +: C_DATA_WIDTH])) |-> $stable(O)
            );
        end
    endgenerate

    // O stays stable when all mux inputs stay stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(S) && $stable(A)) |-> $stable(O)
    );

endmodule