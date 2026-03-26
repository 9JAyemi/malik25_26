module sky130_fd_sc_ls__o2111ai_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic Y
);

    wire [8:0] input_signals;
    assign input_signals = {A1, A2, B1, C1, D1, VPWR, VGND, VPB, VNB};

    // Exact all-ones on the concatenated inputs must drive Y high.
    check_all_inputs_one_drives_y_high: assert property (
        @(posedge clk) (input_signals === 9'h1ff) |-> (Y === 1'b1)
    );

    // Any input pattern other than exact all-ones must drive Y unknown.
    check_non_all_ones_drive_y_unknown: assert property (
        @(posedge clk) (input_signals !== 9'h1ff) |-> (Y === 1'bx)
    );

    // A high Y can only come from the exact all-ones input pattern.
    check_y_high_requires_all_inputs_one: assert property (
        @(posedge clk) (Y === 1'b1) |-> (input_signals === 9'h1ff)
    );

    // The RTL never drives a known zero on Y.
    check_y_never_known_zero: assert property (
        @(posedge clk) (Y !== 1'b0)
    );

endmodule