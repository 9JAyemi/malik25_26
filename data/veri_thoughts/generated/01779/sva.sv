module uart_1wire_sva (
    input logic c,
    input logic w,
    input logic [2:0] a,
    input logic [31:0] wd,
    input logic [31:0] rd,
    input logic uart
);
    // rd follows wd unless w&&a[2], then rd is 0.
    check_rd_function: assert property (
        @(posedge c) rd == ((w && a[2]) ? 32'd0 : wd)
    );

    // uart is 1 unless w&&a[2], then uart mirrors c.
    check_uart_function: assert property (
        @(posedge c) uart == ((w && a[2]) ? c : 1'b1)
    );

    // In non-UART mode (!(w&&a[2])) rd=wd and uart=1.
    check_non_uart_mode_outputs: assert property (
        @(posedge c) !(w && a[2]) |-> ((rd == wd) && (uart == 1'b1))
    );

    // In UART mode (w&&a[2]) rd=0 and uart=c.
    check_uart_mode_outputs: assert property (
        @(posedge c) (w && a[2]) |-> ((rd == 32'd0) && (uart == c))
    );

    // If uart is 0, then w&&a[2] must hold and c must be 0.
    check_uart_low_implies_mode_and_c_low: assert property (
        @(posedge c) (uart == 1'b0) |-> ((w && a[2]) && (c == 1'b0))
    );

    // If rd is 0, it is due to UART mode or wd being 0.
    check_rd_zero_origin: assert property (
        @(posedge c) (rd == 32'd0) |-> ((w && a[2]) || (wd == 32'd0))
    );

    // When w is HIGH and a[2] is LOW, rd=wd and uart=1.
    check_w_high_a2_low_outputs: assert property (
        @(posedge c) (w && !a[2]) |-> ((rd == wd) && (uart == 1'b1))
    );

    // When w is LOW, rd=wd and uart=1.
    check_w_low_outputs: assert property (
        @(posedge c) (!w) |-> ((rd == wd) && (uart == 1'b1))
    );
endmodule